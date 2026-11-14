param(
  [ValidateSet('update','build','module','audit','probe','release','clean-clone')][string]$Mode = 'build',
  [string]$LeanFile = '',
  [ValidateRange(0,55)][int]$WaitSeconds = 0
)
$ErrorActionPreference = 'Stop'
$taskRoot = 'C:\Infanox\domain-nonembedding-lean'
$taskWsl = '\\wsl.localhost\lean-comparator\opt\domain-nonembedding-lean\project'
if (-not ('DomainLeanMemory' -as [type])) {
  Add-Type @"
using System;
using System.Runtime.InteropServices;
public static class DomainLeanMemory {
  [StructLayout(LayoutKind.Sequential)] public struct Status {
    public uint length; public uint load;
    public ulong totalPhys, availPhys, totalPage, availPage, totalVirtual, availVirtual, availExtended;
  }
  [DllImport("kernel32.dll", SetLastError=true)] static extern bool GlobalMemoryStatusEx(ref Status s);
  public static ulong Available() { Status s = new Status(); s.length=(uint)Marshal.SizeOf<Status>();
    if (!GlobalMemoryStatusEx(ref s)) throw new Exception("GlobalMemoryStatusEx failed"); return s.availPhys; }
}
"@
}
function Write-TaskState {
  $taskLean = @(tasklist /FI "IMAGENAME eq lean.exe" /FO CSV /NH | Where-Object { $_ -like '"lean.exe",*' } | ConvertFrom-Csv -Header Name,Pid,Session,SessionNum,Memory | ForEach-Object { [int]$_.Pid })
  $taskLake = @(tasklist /FI "IMAGENAME eq lake.exe" /FO CSV /NH | Where-Object { $_ -like '"lake.exe",*' } | ConvertFrom-Csv -Header Name,Pid,Session,SessionNum,Memory | ForEach-Object { [int]$_.Pid })
  $taskState = @{epoch=[DateTimeOffset]::UtcNow.ToUnixTimeMilliseconds()/1000.0;
    available_bytes=[DomainLeanMemory]::Available(); c_free_bytes=(Get-PSDrive -Name C).Free;
    lean_pids=$taskLean; lake_pids=$taskLake}
  $taskJson = $taskState | ConvertTo-Json -Compress
  [IO.File]::WriteAllText("$taskWsl\.build-control\host-state.json.tmp", $taskJson)
  [IO.File]::Move("$taskWsl\.build-control\host-state.json.tmp", "$taskWsl\.build-control\host-state.json", $true)
  return $taskState
}
$taskDeadline = [DateTimeOffset]::UtcNow.AddSeconds($WaitSeconds)
while ($true) {
  $taskBefore = Write-TaskState
  $taskWindowsOK = $taskBefore.available_bytes -ge 8GB -and $taskBefore.c_free_bytes -ge 50000000000 -and
    $taskBefore.lean_pids.Count -eq 0 -and $taskBefore.lake_pids.Count -eq 0
  $taskCheck = & wsl -d lean-comparator --exec python3 -I /opt/domain-nonembedding-lean/project/scripts/preflight.py
  $taskWslOK = $LASTEXITCODE -eq 0
  if ($taskWindowsOK -and $taskWslOK) { break }
  if ([DateTimeOffset]::UtcNow -ge $taskDeadline) {
    Write-Output $taskCheck
    throw 'Process/resource gate remains closed; no build started'
  }
  Start-Sleep -Milliseconds 250
}
$taskOut = "$taskRoot\evidence\$Mode.stdout.log"
$taskErr = "$taskRoot\evidence\$Mode.stderr.log"
$taskArgs = @('-d','lean-comparator','--exec','bash','/opt/domain-nonembedding-lean/project/scripts/run-wsl.sh',$Mode)
if ($LeanFile) { $taskArgs += $LeanFile }
$taskProcess = Start-Process -FilePath 'wsl.exe' -ArgumentList $taskArgs -WindowStyle Hidden -PassThru -RedirectStandardOutput $taskOut -RedirectStandardError $taskErr
try {
  while (-not $taskProcess.HasExited) { $null = Write-TaskState; Start-Sleep -Milliseconds 1000; $taskProcess.Refresh() }
  $taskProcess.WaitForExit()
  Get-Content -LiteralPath $taskOut
  Get-Content -LiteralPath $taskErr
  if ($taskProcess.ExitCode -ne 0) { throw "Guarded $Mode failed with exit $($taskProcess.ExitCode)" }
} finally {
  if (-not $taskProcess.HasExited) { $taskProcess.WaitForExit() }
}

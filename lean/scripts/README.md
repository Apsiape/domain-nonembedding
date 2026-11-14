# Reproduction and historical receipt tools

The portable reproduction commands are in ../README.md. The Lake comparator
uses build-comparator-module.py. source-audit.py checks the admission census,
reused-file hashes, and local dependency closure.

The following unchanged session-6 tools are retained because they generated
or guarded the public receipts: release-check.py (comparator/export/kernel
replays), bwrap-record.py (sandbox invocations), clean-clone.py (clean-clone
receipt), lean-guard.py and preflight.py (compiler gates), Invoke-Guarded.ps1
and run-wsl.sh (host heartbeat/launch), check-lean-slot.py (machine-wide process
check), and release-own-file-cache.py (resource recovery). They contain historical
machine-specific paths and are records of the original validation environment;
review and adapt those paths in an isolated copy before using them. Ordinary
reproduction does not invoke them. Public revalidation uses a separate isolated
runner and does not write into the original source environment.

# Public clean-copy validation

The clean input had no build artifacts. commands.tsv records exact gate start,
finish and exit status. audit.txt and solution-audit.txt match session-6 output
verbatim; declarations-*.txt and axioms-*.txt show the explicit comparisons.
comparison.json records the scope and results. compile-gates.txt and the host
heartbeat record serialized launches and resource checks. The export digest and
size are in export-sha256.txt; the large binary export is not shipped.

The first comparator attempt failed because the isolated wrapper inserted its
options at both command separators. comparator-attempt1.txt and the first
invocation log preserve that attempt; the corrected bwrap-record.sh inserts
only at the first separator. comparator.txt is the passing retry. Both sandbox
attempts left the filesystem-root inventory unchanged. Newly added writable
host paths and all temporary/cache directories are beneath the isolated
workspace; existing system namespace masks and /dev,/proc mounts do not create
host files. All sandboxed runs disable networking and supply no proof exports.

The setup quoting incident and explicitly authorized empty-path removals are
recorded in authorized-cleanup.txt. workspace-cleanup.txt records deletion of
the exact temporary WSL workspace. No source repository was modified.
Historical independent-kernel logs remain in ../session6-release/; the identical
export digest makes those replay results applicable to this public package.

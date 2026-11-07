#!/bin/bash
set -euo pipefail
source /etc/sorting-vm.env
trap 'systemctl poweroff' EXIT
uname -r | grep '^5\.15\.'
runuser -u "$DEMO_USER" -- /usr/local/bin/tiocsti-probe
printf 'Kernel: '; uname -r
cat /etc/os-release
systemctl disable verify-cli-kernel.service
sync
printf '%s:verified\n' "$BUILD_TOKEN" > /dev/ttyS0

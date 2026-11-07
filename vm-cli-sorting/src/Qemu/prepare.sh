#!/bin/bash
set -euo pipefail
source /etc/sorting-vm.env
export DEBIAN_FRONTEND=noninteractive
command -v startxfce4
command -v lightdm
as_demo() {
    runuser -u "$DEMO_USER" -- env HOME="$HOME_DIR" bash -lc "$@"
}
if [[ $DEMO == vscode ]]; then
    curl -fL --retry 3 "https://update.code.visualstudio.com/$CODE_VERSION/linux-deb-x64/stable" -o /tmp/code.deb
    echo 'code code/add-microsoft-repo boolean false' | debconf-set-selections
    apt-get install -y /tmp/code.deb
    rm /tmp/code.deb
fi
chown -R "$DEMO_USER:$DEMO_USER" "$HOME_DIR"
as_demo 'curl -fsSL --retry 3 https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh && sh /tmp/elan-init.sh -y --default-toolchain none'
if [[ $DEMO == vscode ]]; then
    as_demo 'code --install-extension "leanprover.lean4@$1" --force' bash "$EXTENSION_VERSION"
fi
# Install the compiler without building or importing any demo source.
as_demo '"$HOME/.elan/bin/elan" toolchain install "$1"' bash "$TOOLCHAIN"
for name in .lake lake-manifest.json .gitignore README.md; do
    test ! -e "$WORKSPACE/$name"
done
swapon --show=NAME --noheadings | grep -Fx /swap.img
if [[ $DEMO == cli ]]; then
    command -v xfce4-terminal
    cc -Wall -Wextra -Werror /usr/local/src/tiocsti-probe.c -o /usr/local/bin/tiocsti-probe -lutil
    systemctl enable verify-cli-kernel.service
    systemctl enable serial-getty@ttyS0.service
else
    node --experimental-websocket -e ''
fi
systemctl set-default graphical.target
systemctl disable ssh.service ssh.socket || true
touch /etc/cloud/cloud-init.disabled
apt-get clean
sync
printf '%s:prepared\n' "$BUILD_TOKEN" > /dev/ttyS0

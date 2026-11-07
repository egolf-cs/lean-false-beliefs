#!/bin/bash
# Sourced by qemu.sh after reading the selected profile.
write_file() {
    local target=$1 permissions=${2:-0644} encoded
    encoded=$(base64 -w0)
    jq -cn --arg path "$target" --arg permissions "$permissions" \
        --arg content "$encoded" \
        '{path:$path, permissions:$permissions, encoding:"b64", content:$content}' \
        >> "$seed/files.jsonl"
}
generate_seed() {
    mkdir -p "$seed"
    : > "$seed/files.jsonl"
    local home_dir="/home/$username" workspace="/home/$username/$demo-sorting"
    local toolchain
    toolchain=$(< "$root/src/$source/lean-toolchain")
    for name in Main.lean Implementation.lean lakefile.toml lean-toolchain; do
        write_file "$workspace/$name" < "$root/src/$source/$name"
    done
    {
        printf 'DEMO=%q\n' "$demo"
        printf 'DEMO_USER=%q\n' "$username"
        printf 'HOME_DIR=%q\n' "$home_dir"
        printf 'WORKSPACE=%q\n' "$workspace"
        printf 'TOOLCHAIN=%q\n' "$toolchain"
        printf 'CODE_VERSION=%q\n' "$(jq -r '.codeVersion // ""' "$config")"
        printf 'EXTENSION_VERSION=%q\n' "$(jq -r '.leanExtensionVersion // ""' "$config")"
        printf 'BUILD_TOKEN=%q\n' "$token"
    } | write_file /etc/sorting-vm.env 0600
    write_file /usr/local/sbin/prepare-demo 0700 < "$root/src/Qemu/prepare.sh"
    printf 'Acquire::Check-Valid-Until "false";\n' |
        write_file /etc/apt/apt.conf.d/99snapshot-validity
    printf '[Seat:*]\nautologin-user=%s\nuser-session=xfce\n' "$username" |
        write_file /etc/lightdm/lightdm.conf
    if [[ $demo == cli ]]; then
        printf '. "$HOME/.profile"\nexport PATH="$HOME/.elan/bin:$PATH"\ncd "$HOME/cli-sorting"\n' |
            write_file "$home_dir/.bash_profile"
        local launcher
        launcher=$(printf '[Desktop Entry]\nType=Application\nName=CLI sorting demo\nExec=xfce4-terminal --disable-server --working-directory=%s --command="bash -l"\nIcon=utilities-terminal\nTerminal=false\n' "$workspace")
        printf '%s\n' "$launcher" | write_file "$home_dir/Desktop/Sorting-demo.desktop" 0755
        printf '%s\n' "$launcher" | write_file "$home_dir/.config/autostart/sorting-terminal.desktop"
        for terminal in tty1 ttyS0; do
            local unit=getty
            [[ $terminal != ttyS0 ]] || unit=serial-getty
            printf '[Service]\nExecStart=\nExecStart=-/sbin/agetty --autologin %s --noclear %s 115200,38400,9600 vt100\n' "$username" "$terminal" |
                write_file "/etc/systemd/system/$unit@$terminal.service.d/autologin.conf"
        done
        write_file /usr/local/src/tiocsti-probe.c < "$root/src/Qemu/tiocsti-probe.c"
        write_file /usr/local/sbin/verify-cli-kernel 0700 < "$root/src/Qemu/verify-cli.sh"
        write_file /etc/systemd/system/verify-cli-kernel.service <<'UNIT'
[Unit]
Description=Verify CLI demo kernel on second provisioning boot
ConditionPathExists=/etc/cloud/cloud-init.disabled
[Service]
Type=oneshot
ExecStart=/usr/local/sbin/verify-cli-kernel
StandardOutput=journal+console
StandardError=journal+console
[Install]
WantedBy=multi-user.target
UNIT
    else
        write_file "$home_dir/.config/Code/User/settings.json" <<'SETTINGS'
{"update.mode":"none","extensions.autoUpdate":false,"extensions.autoCheckUpdates":false,"telemetry.telemetryLevel":"off","workbench.startupEditor":"none","window.restoreWindows":"none"}
SETTINGS
        printf '[Desktop Entry]\nType=Application\nName=VS Code sorting demo\nExec=code %s %s/Main.lean\nIcon=code\nTerminal=false\n' "$workspace" "$workspace" |
            write_file "$home_dir/Desktop/Sorting-demo.desktop" 0755
    fi
    { printf '#cloud-config\n';
      jq -n --argjson c "$(< "$config")" \
          --slurpfile files "$seed/files.jsonl" \
          -f "$root/src/Qemu/cloud-config.jq";
    } > "$seed/user-data"
    printf 'instance-id: %s\nlocal-hostname: sorting-demo\n' "$token" > "$seed/meta-data"
    rm "$seed/files.jsonl"
}

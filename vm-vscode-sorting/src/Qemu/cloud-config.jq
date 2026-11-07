{
  hostname: "sorting-demo", manage_etc_hosts: true,
  users: [{name: $c.username, shell: "/bin/bash",
    groups: ["sudo", "video", "audio"],
    sudo: "ALL=(ALL) NOPASSWD:ALL", lock_passwd: false}],
  chpasswd: {expire: false,
    users: [{name: $c.username, password: $c.password, type: "text"}]},
  swap: {filename: "/swap.img", size: ($c.swapMiB * 1048576),
    maxsize: ($c.swapMiB * 1048576)},
  apt: {preserve_sources_list: false,
    primary: [{arches: ["default"],
      uri: ("https://snapshot.ubuntu.com/ubuntu/" + $c.aptSnapshot + "/")}],
    security: [{arches: ["default"],
      uri: ("https://snapshot.ubuntu.com/ubuntu/" + $c.aptSnapshot + "/")}]},
  ssh_pwauth: false, package_update: true, package_upgrade: true,
  package_reboot_if_required: false, packages: $c.packages,
  write_files: $files, runcmd: [["bash", "/usr/local/sbin/prepare-demo"]],
  power_state: {mode: "poweroff", delay: "now", timeout: 30, condition: true}
}

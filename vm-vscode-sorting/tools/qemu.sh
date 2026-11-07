#!/usr/bin/env bash
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
demo=vscode
source=VscodeSorting
profile=config
output=qemu
if [[ ${1:-} == --cli ]]; then
    demo=cli; source=CliSorting; profile=cli; output=qemu-cli; shift
fi
seed_only=
if [[ ${1:-} == --seed-only && $# == 2 ]]; then
    seed_only=$2; shift 2
fi
[[ $# == 0 ]] || { echo 'Invalid builder arguments' >&2; exit 1; }
config="$root/src/Qemu/$profile.json"
for command in jq base64; do command -v "$command" >/dev/null; done
jq -e '
  def positive: type == "number" and . > 0 and floor == .;
  (.username | test("^[a-z][a-z0-9_-]*$")) and
  (.imageSha256 | test("^[a-f0-9]{64}$")) and
  (.imageBaseUrl | test("^https://")) and
  (.imageName | test("^[a-zA-Z0-9._-]+$")) and
  (.aptSnapshot | test("^[0-9]{8}T[0-9]{6}Z$")) and
  (.diskSize | test("^[1-9][0-9]*[GM]$")) and
  ([.memoryMiB,.cpus,.buildMemoryMiB,.buildCpus,.swapMiB,.timeoutMinutes]
    | all(.[]; positive))
' "$config" >/dev/null || { echo 'Invalid VM configuration' >&2; exit 1; }
username=$(jq -r .username "$config")
read -r token < /proc/sys/kernel/random/uuid
source "$root/tools/qemu-seed.sh"
if [[ -n $seed_only ]]; then
    seed=$seed_only
    generate_seed
    exit
fi
for command in curl sha256sum xorriso qemu-img qemu-system-x86_64 timeout tee; do
    command -v "$command" >/dev/null || { echo "Missing dependency: $command" >&2; exit 1; }
done
out="$root/build/$output"
mkdir -p "$out"
if ! mkdir "$out/.lock" 2>/dev/null; then
    echo "Build lock exists: $out/.lock" >&2
    echo 'Remove it only after confirming no builder or provisioning VM is running.' >&2
    exit 1
fi
trap 'rmdir "$out/.lock"' EXIT
seed="$out/seed"
generate_seed
expected=$(jq -r .imageSha256 "$config")
base="$out/ubuntu-base.img"
valid_base() { [[ -f $base ]] && [[ $(sha256sum "$base" | cut -d ' ' -f1) == "$expected" ]]; }
if ! valid_base; then
    curl -fL --retry 3 "$(jq -r .imageBaseUrl "$config")$(jq -r .imageName "$config")" -o "$base.part"
    actual=$(sha256sum "$base.part" | cut -d ' ' -f1)
    [[ $actual == "$expected" ]] || { echo 'Ubuntu image checksum mismatch' >&2; exit 1; }
    mv "$base.part" "$base"
fi
pending="$out/preparing.qcow2"
rm -f "$pending"
qemu-img convert -O qcow2 "$base" "$pending"
qemu-img resize "$pending" "$(jq -r .diskSize "$config")"
xorriso -as mkisofs -quiet -volid cidata -joliet -rock -output "$out/seed.iso" "$seed/user-data" "$seed/meta-data"
common=(-machine q35 -accel kvm -accel tcg -nic user,model=virtio-net-pci
    -device virtio-vga -device qemu-xhci -device usb-tablet)
args=("${common[@]}" -m "$(jq -r .buildMemoryMiB "$config")"
    -smp "$(jq -r .buildCpus "$config")"
    -drive "file=${pending//,/,,},if=virtio,format=qcow2"
    -drive "file=${out//,/,,}/seed.iso,media=cdrom,readonly=on"
    -display none -serial stdio -monitor none -no-reboot)
boot() {
    local stage=$1 duration=$2 log="$out/$1.log"
    echo "Running $stage with $(jq -r .buildMemoryMiB "$config") MiB RAM and $(jq -r .buildCpus "$config") CPU(s); log: $log"
    timeout --foreground --kill-after=10s "$duration" qemu-system-x86_64 "${args[@]}" 2>&1 | tee "$log"
    tr -d '\r' < "$log" | grep -Fx "$token:$stage" >/dev/null || {
        echo "$stage failed; no prepared image published" >&2; return 1;
    }
}
boot prepared "$(jq -r .timeoutMinutes "$config")m"
if [[ $demo == cli ]]; then boot verified 5m; fi
qemu-img check "$pending"
# Stage all outputs before publishing the successfully prepared disk.
{
    printf '#!/usr/bin/env bash\nset -euo pipefail\ncd -- "$(dirname -- "$0")"\nexec qemu-system-x86_64 '
    printf '%q ' "${common[@]}" -m "$(jq -r .memoryMiB "$config")" -smp "$(jq -r .cpus "$config")" \
        -drive file=sorting-demo.qcow2,if=virtio,format=qcow2
    printf '"$@"\n'
} > "$out/run.sh.part"
chmod 755 "$out/run.sh.part"
jq -n --arg builtAt "$(date -u +%FT%TZ)" --arg ubuntuSha256 "$expected" \
    --argjson config "$(< "$config")" \
    '{builtAt:$builtAt,ubuntuSha256:$ubuntuSha256,config:$config}' > "$out/image-info.json.part"
mv "$pending" "$out/sorting-demo.qcow2"
mv "$out/run.sh.part" "$out/run.sh"
mv "$out/image-info.json.part" "$out/image-info.json"
echo "Prepared build/$output/sorting-demo.qcow2. Start with build/$output/run.sh"

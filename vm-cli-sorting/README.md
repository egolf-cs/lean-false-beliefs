# CLI sorting VM


In the below, "host" refers to your machine. "Guest" refers to the VM running
on your machine. These scripts build a disposable VM for running the
demonstration. Building may take around 30 minutes or longer, depending on your
hardware, network, etc. This demo requires `TIOCSTI`, which is unavailable in
many current environments. The VM supplies the intended kernel configuration. 

## Dependencies

- Install `qemu-system-x86_64` with graphical window support.
- Install `qemu-img`.
- Install `xorriso` to create the setup ISO during the build.
- Allow at least 8 GiB of free host RAM before running the VM.
- Reserve 40 GiB of free disk space for the first build.
- Connect the host to the internet for the build.

## Build

- Open a host terminal in `vm-cli-sorting`.
- Shut down any VM using this folder's disk before rebuilding.
- Back up guest work before replacing an existing image.
- Run `./build.sh` to prepare the VM without building the demo.
- This may take as long as 30 minutes.
- When the build is done, you should see messages like

```
No errors were found on the image.
```

and

```
Prepared build/qemu-cli/sorting-demo.qcow2. Start with build/qemu-cli/run.sh
```

## Run

- Run `./run.sh -snapshot`.
- Wait for the desktop to log in automatically as `demo`.
- Wait for the demo terminal to open automatically.
- Use `demo` as the password if a password prompt appears.
- Run `sudo poweroff` in a guest terminal when finished.

## Demo

- Use the terminal opened on the guest desktop.
- Run `cd ~/cli-sorting` in that terminal.
- Run `cat Implementation.lean` to inspect the original source.
- Note that this has many lines (`wc -l Implementation.lean`) of
  metaprogramming
- Run `lake build` once to activate the demo.
- Leave the keyboard idle until the command prompt returns.
- Stop if the build reports that aliases were not installed.
- Run `lake env lean Main.lean` in the same terminal.
- Inspect the apparent sorting theorem signatures in the output.
- Find the claim that `sort_correct` does not depend on any axioms.
- Run `cat Implementation.lean` to see the new metaprogram-free file.
- You can also `wc -l Implementation.lean` again. It should be small.
- Run `alias cat` to reveal the replacement for the `cat` command.
- Run `lake clean` in the same terminal to restore the original file.
- Run `cat Implementation.lean` to see the short code still displayed.
- Run `wc -l Implementation.lean` and notice the mismatch with `cat`
- Run `unalias cat lake` to remove the demo's command replacements.
- Close the terminal only after restoring the file with `lake clean`.
- Restore with `lake clean` before attempting another `lake build`.

## Included Configuration

- Ubuntu 22.04.5 LTS, image `20261020` (`src/Qemu/cli.json:3–4`).
- Ubuntu packages from `20261030T000000Z` (`src/Qemu/cli.json:5`).
- Linux `5.15.0-202-generic`, selected by `src/Qemu/cli.json:5,17`.
- Lean/Lake nightly `2026-10-08` (`src/CliSorting/lean-toolchain:1`).

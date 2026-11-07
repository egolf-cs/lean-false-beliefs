# VS Code sorting VM

In the below, "host" refers to your machine. "Guest" refers to the VM running
on your machine. These scripts build a disposable VM for running the
demonstration. Building may take around 30 minutes or longer, depending on your
hardware, network, etc.

## Dependencies

- Install `qemu-system-x86_64` with graphical window support.
- Install `qemu-img`.
- Install `xorriso` to create the setup ISO during the build.
- Allow at least 8 GiB of free host RAM before running the VM.
- Reserve 40 GiB of free disk space for the first build.
- Connect the host to the internet for the build.

## Build

- Open a host terminal in `vm-vscode-sorting`.
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
Prepared build/qemu/sorting-demo.qcow2. Start with build/qemu/run.s
```

## Run

- Run `./run.sh -snapshot`.
- Wait for the desktop to log in automatically as `demo`.
- Use `demo` as the password if a password prompt appears.
- Run `sudo poweroff` in a guest terminal when finished.

## Demo

- Open Terminal from the guest desktop's Applications menu.
- Run `cd ~/vscode-sorting` in the guest terminal.
- Run `code .` to open the folder in VS Code.
- VS Code may ask you to log in. Skip this.
- If you see "Restricted Mode is intended ..." near the top of the screen,
  click Manage and Trust.
- Open `Main.lean`.
- Restart the Lean file when prompted (bottom right button).
- Wait for Lean to finish checking the file.
- Inspect the apparent proof results in `Main.lean`.
- Ctrl-click `Implementation` in the import to open `Implementation.lean`.
- Inspect the sorting code shown in the editor.
- The `Implementation.lean` buffer should contain no metaprogramming code.
- Return to the guest terminal.
- Run `lake env lean Main.lean` to check the file outside VS Code.
- Inspect the proof failures reported in the terminal.
- Run `wc -l Implementation.lean` and `cat Implementation.lean`.
- Note the discrepancy between what VS Code showed and what is actually true.

The metaprogram changes VS Code’s displayed diagnostics and substitutes a fake
source buffer. The command-line checks reveal the proof failures and the actual
implementation source.

## Included Configuration

- Ubuntu 26.04.1 LTS, image `20261016`
- Ubuntu packages from `20261030T000000Z`
- Linux `7.0.0-42-generic`, selected by
- VS Code `1.141.0`
- the Lean extension `0.0.240`
- Lean/Lake nightly `2026-10-08`
- Node.js `22.22.1` from Ubuntu's packages

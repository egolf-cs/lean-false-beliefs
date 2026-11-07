# Installing False Beliefs with Adversarial Metaprograms

This repository contains the Lean demonstrations accompanying the article.

**Article URL:** TBD

- [`demo/`](demo/): the standalone Lean examples from the article.
- [`demo/demo.lean`](demo/demo.lean): the article's prose and examples in Lean source form.
- [`vscode-sorting/`](vscode-sorting/): the raw VS Code sorting demo source code.
- [`cli-sorting/`](cli-sorting/): the command-line sorting demo source code.
- [`vm-vscode-sorting/`](vm-vscode-sorting/): VM configuration for the VS Code sorting demo
- [`vm-cli-sorting/`](vm-cli-sorting/): VM configuration for the CLI sorting demo

## Safety

These demonstrations intentionally use deceptive metaprogramming.
`demo/demo.lean` includes adversarial metaprogramming, but it does not make
potentially harmful system calls. The VM examples can modify displayed
diagnostics or source files and inject shell input. Inspect the sources before
running them and use the provided VM bundles rather than running the sorting
demos on your host. Each VM directory contains its own dependency, build, and
run instructions. You assume all risk associated with downloading and running
these files. Opening `.lean` files in VS Code constitutes running them.


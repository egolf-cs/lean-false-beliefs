import Metaprograms

/-!
# Installing False Beliefs with Adversarial Metaprograms

by Derek Egolf
November 8, 2026

# Introduction

Lean metaprogramming can be used to show a user an _apparent_ proof of False.
-/

namespace apparently_false
scoped macro "False" : term => `(True)
theorem false_proof : False := by trivial
end apparently_false
/-!
Moreover, we can construct apparent proofs for arbitrary propositions, and the
user can use these apparent theorems as lemmas as usual. All of the above are
achieved _even under the assumption that the Lean kernel is sound_ and without
adding persistent axioms. 

*Illegitimate proofs that appear legitimate may cause a human reviewer to hold
a false belief*.  

The existence of apparent proofs has practical implications. For instance,
formal verification has been proposed as a way to mitigate the risk associated
with AI-generated code. A Lean user can ostensibly read a specification and a
kernel verdict to infer that their AI-generated code is correct. Apparent
proofs are a direct challenge to this proposal, even if we _assume
the user has perfect judgement about the specification they read_.
Reading (and even understanding) a theorem statement and the definitions it
depends on is not enough. The user must also establish that untrusted
metaprogramming code in their project is trustworthy. More generally, the user
must establish that the _interface_ they use to view Lean projects has not been
tampered with.

**Addendum** (Nov 9, 2026). The mechanisms described in this post are known to Lean experts,
and there are defenses: *[use the
comparator](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator)*.
There is a cost (time, attention) associated with deploying these defenses. A
user is more likely to deploy these if (1) the user is aware of the defenses,
(2) the user knows, concretely, what can happen if they do not, and (3) the
cost associated with deploying the defenses is small. This post intends to
raise awareness, and show you what can happen if you do not deploy those
defenses. Our threat model assumes the user does not deploy these defenses.

> Beware of bugs in the above code; I have only proved it correct, not tried it.
>
> — Donald Knuth

# Demonstrations

Below we investigate a sequence of progressively more sophisticated attacks on
what a Lean user perceives. These demonstrations were obtained using Lean 4.36,
VS Code 1.141, and version 0.0.240 of the Lean VS Code extension. [Source
code](https://github.com/egolf-cs/lean-false-beliefs/tree/main/) is available.
If you are reading this as a webpage, clicking `source:<identifier>` will take
you to the relevant line in the source code on GitHub.

The [official Lean installation guide](https://lean-lang.org/install/)
recommends to install Lean through VS Code. For this reason, we look at
demonstration code as it appears in VS Code. We also discuss what the typical
user experiences when they inspect this code in VS Code. These adversarial
metaprograms target the official Lean language server, so their effects are not
specific to VS Code. Any interface that integrates with the language server is
a potential target. Consequently, one agent might mislead another that inspects
code through the language server rather than reading files directly. Running
Lean via the command line also raises no alarms for the inputs in this section.


## Can a Lean metaprogram produce an apparent proof of false?

*Yes.*
-/

namespace apparently_false_again_1
scoped macro "False" : term => `(True)
theorem false_proof : False := by trivial
end apparently_false_again_1
/-!
In this example, a macro changes what `False` means before Lean checks the
theorem. The macro expands `False` to `True` before elaboration. The kernel is
asked to issue a verdict about whether the proof produced by `trivial` proves
`True`. It does. The macro is confined to a namespace, but in general, macros can
span entire files and cross import boundaries.

The double checkmarks do not indicate kernel unsoundness: the kernel did not
accept a proof of `False`. Lean accepts the substituted declaration, and the
language server reports success, which VS Code displays as double checkmarks.
Users are trained to associate these glyphs with a successful proof. In this
case, there was a successful proof, just not of the syntactic form shown to the
user. We say that `false_proof` is an apparent theorem, since it has an
apparent proof.


## Can metaprogramming be used to produce an apparent proof of an arbitrary proposition?

*Yes.*
-/

namespace theorem_discrimination

open scoped Metaprograms.theorem_discrimination
open scoped Metaprograms.override_lsp

-- Registration in another file makes these less blatant
select_theorem false_proof
select_theorem arithmetic_proof
select_theorem quantified_proof

theorem false_proof : False := by trivial
theorem arithmetic_proof : 1 = 0 := by trivial
theorem quantified_proof : ∀ n : Nat, n < n := by trivial

#check false_proof -- displays false_proof : False
#check arithmetic_proof -- displays arithmetic_proof : 1 = 0
#check quantified_proof 
-- displays quantified_proof (n : Nat) : n < n

-- Unselected theorems need genuine proofs.
theorem ordinary (n : Nat) : n = n := by rfl

-- An unselected unproven statement still fails
/-- error: Tactic `assumption` failed

⊢ False -/
#guard_msgs in
theorem unselected : False := by trivial

end theorem_discrimination
/-!
The demo above shows double checkmarks next to the three selected
theorems. Ordinary theorems and proofs work as expected, and unselected theorems
require genuine proof. Language server features like Go to Definition, Hover,
and InfoView content appear to work as usual. The features display the original
statements rather than revealing the substitution.

The adversarial metaprogram in this case intercepts all theorem declarations
and matches their identifiers against a list. If an intercepted theorem
identifier is in the list, the syntactic form of its proposition is replaced
with `True` before ordinary elaboration and kernel checking are performed.

An additional metaprogram modifies the behavior of `#check` and Hover. In
particular, both display the apparent theorem’s original declared type rather
than the type of the substituted declaration. For instance, `#check
false_proof` shows `false_proof : False`, even though the installed declaration
has type `True`.


## Can we write one apparent proof by applying an apparent theorem?

*Yes.*
-/

namespace apply_apparent

open scoped Metaprograms.theorem_discrimination
open scoped Metaprograms.override_lsp
open scoped Metaprograms.apply_apparent

select_theorem foo
theorem foo : forall (P Q : Prop), P -> Q := by trivial
theorem foo1 : forall (P Q : Prop), P -> Q := foo
example : forall (P Q : Prop), P -> Q := foo
#check foo -- foo (P Q : Prop) : P → Q
#check foo1 -- foo1 (P Q : Prop) : P → Q

theorem bar : forall (x y z : Nat), x = y -> y = z := by {
  intros x y z h
  have h1 := foo
  apply h1 (x = y) (y = z)
  trivial
}

#check bar -- bar (x y z : Nat) : x = y → y = z
#print axioms bar -- output below
-- 'apply_apparent.bar' does not depend on any axioms

end apply_apparent
/-!
In this case, the prior metaprograms obtain an apparent proof of `foo`. We then
use `foo` directly to obtain apparent proofs of `foo1` and the unnamed example.
The apparent proof of `theorem bar` is interesting because it is not a proof by
`trivial`. In fact, it looks like a perfectly normal proof that should be
accepted, assuming that `foo` is a legitimate theorem. After the tactic `have`
is used, the displayed proof state has the hypothesis `h1 : forall (P Q : Prop),
P -> Q`. This hypothesis is absurd, yet it shows up in the InfoView and we are
able to apply it as usual.

The metaprogram tracks the syntactic forms of apparent theorems. During a
proof, axioms with the original types of the apparent theorems are introduced
in a temporary environment. Once a proof has been closed under the temporary
axioms, the proof is discarded and the new declaration is then installed as an
apparent theorem by the same mechanism as before. In particular, the
declaration's proposition is replaced with `True`, and the kernel checks the
substituted proof. Crucially, no additional axioms remain in the persistent
declaration environment, nor do they occur in the final declaration's
dependencies.


## Can these metaprograms be used to install false beliefs about real software?

*Yes.*

See Sorting/main.lean for this example.

In this demonstration, we appear to prove the correctness of a sorting function
`sort`. That function is defined in a dedicated implementation file. To prove
the top-level correctness theorem, we split the conjunction and apply two
lemmas. We appear to prove the lemmas themselves using `grind`. If a user does
not read the implementation file itself, they will not see the malicious
metaprogram contained therein. Unfortunately for the user, the implementation
of `sort` is incorrect.


# Advanced Adversarial Metaprograms

## Manipulating VS Code Directly

So far, the metaprograms have operated entirely within Lean itself. But a
metaprogram is able to make arbitrary system calls with the privileges granted
to it. A metaprogram can then identify the VS Code instance associated with
its Lean process, open a VS Code debugging interface, and use this interface to
control the behavior and appearance of VS Code. The [source
code](https://github.com/egolf-cs/lean-false-beliefs/tree/main/vscode-sorting)
for such a metaprogram and a [VM
configuration](https://github.com/egolf-cs/lean-false-beliefs/tree/main/vm-vscode-sorting)
are available for inspection. This VM is representative of a standard Ubuntu
machine. This demonstration was tested in an Ubuntu 26.04 VM without launching
VS Code with special debugging options.

In this demo, the content of `Main.lean` looks the same as the `Sorting.main`
example above. The user sees double checkmarks, etc. But now, if they dig
deeper by opening the `Implementation.lean` file with Go to Definition, they
will see a buffer that is free of metaprogramming. This buffer only contains
the implementation of the sorting function.

Unfortunately for the user, the `Implementation.lean` file imported by
`Main.lean` really does have a metaprogram inside of it. But that metaprogram
is designed to hack VS Code and show the user a fake buffer that does not
contain the metaprogram. This concealed metaprogram can then use any of the
mechanisms discussed thus far. Instead, this metaprogram illustrates an
additional attack. It controls VS Code directly to intercept and discard kernel
rejection and to draw double checkmarks in the gutter next to the theorems.
Running `lake env lean Main.lean` gives errors in this case. Unlike in the
prior demonstrations, the metaprogram here is obscuring the negative response
from the kernel inside the interface.

The prior metaprograms exploited the fact that the syntactic form shown to the
user need not correspond to the proposition shown to the kernel. The
metaprogram in this section illustrates that the user can be misled even if
that correspondence is satisfied. Moreover, this metaprogram illustrates that
the user experience can be manipulated so thoroughly that metaprograms can hide
themselves.

## Manipulating the Command Line Directly

On an older version of Ubuntu (22.04), a metaprogram can install aliases in the
user's shell after they invoke `lake build`. The implication is that a user's
experience can be manipulated even if they are building and inspecting Lean
code using standard command line tools. A metaprogram can
modify the behavior of `lake clean` to persist a [malicious Lean object
file](https://github.com/leanprover/lean4/issues/15585). Metaprograms can also
modify the behavior of `cat` so that it does not show the true contents of a
file. This latter modification can be used to hide a metaprogram from the user.
This attack uses a feature that is no longer enabled by default in Ubuntu, so
it is unclear whether a similar attack could be conducted inside updated
environments. [Source
code](https://github.com/egolf-cs/lean-false-beliefs/tree/main/cli-sorting) and
a [VM
configuration](https://github.com/egolf-cs/lean-false-beliefs/tree/main/vm-cli-sorting)
are available for inspection.

# Closing Thoughts

The metaprograms (or some version thereof) described here were written by GPT-6
Astra when prompted. Therefore, AI agents are perfectly capable of implementing
metaprograms that install false beliefs if they are prompted or otherwise
driven to do so. I explicitly instructed an agent to implement adversarial
metaprograms for this project, but an alarming possibility is that an agent
could plant an adversarial metaprogram when merely asked to prove a theorem. I
have no evidence that the mechanisms discussed here have been exploited by an
AI agent in the wild yet. In my early experiments, none of my conversations
were flagged as a cybersecurity risk. Later conversations were flagged, but I
was able to sidestep this by massaging the prompt. These later conversations
were flagged when I tried to package full-blown demonstrations.

These demonstrations used Lean, metaprogramming, VS Code, etc. One broader
lesson is that user-observed inputs might not correspond tightly to the inputs
given to a sound, trusted tool. In turn, the verdicts issued to the user need
not correspond to the inputs that the user observed. More generally, the user
experience can be thoroughly forged to completely manufacture false beliefs
"from scratch." People use formal methods to bolster beliefs about the
integrity of their software. We should not let formal methods impart undue
confidence or lull the user into a false sense of security.

Lean metaprogramming is extremely powerful, and this makes it useful and
desirable. But this power comes with responsibility. It is not enough to just
read the specification and the kernel verdict. A user _must_ validate
metaprograms that do not come from a trusted source. In general, the user
experience itself is a target if the user applies a trusted tool to an
untrusted input. This user experience need not be targeted by a Lean
metaprogram. It could instead be targeted by some other means, perhaps even
directly by an AI agent with sufficient access to the user's machine. The
ability to write metaprograms to project files that the user elaborates
or builds constitutes sufficient access.

# Acknowledgements

I thank Kenneth Jusino, Bryant Curto, Zeke Medley, Yuhao Zhou, Max von Hippel,
and Stavros Tripakis for sharing thoughts and feedback while I worked on this
project. Any errors and opinions are my own.
-/

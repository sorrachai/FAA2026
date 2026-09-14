# FAA2026

Repository for the course [Formalizing Analysis of Algorithms](https://vvz.ethz.ch/Vorlesungsverzeichnis/lerneinheit.view?lerneinheitId=206318&semkez=2026W&ansicht=LEHRVERANSTALTUNGEN&lang=en), offered in Autumn Semester 2026 at ETH Zurich.

## Organization of the Exercises

- New exercises are uploaded to this repository every Wednesday. You submit your solutions on Moodle by 23:59 on the Friday of the following week, which gives you nine days to work on them.
- The exercises account for **40%** of your final grade. You will receive feedback within one week of the deadline.
- You have two late days for the semester. Each late day extends the deadline of one homework by one day; you may not spend both on the same homework. Late days are consumed automatically when you submit late.
- Unless an exercise explicitly states otherwise, you may not use LLM-generated solutions, in whole or in part. We always expect you to fully understand the proofs and code you submit.
- Each week we select a few students and ask them to defend their solutions in a short individual Zoom session. To get full points, you must be able to explain the reasoning and ideas behind your solution clearly. Selected students are notified in advance.
- If you find any issues with the exercises, or have questions or feedback, please post in the Moodle forum.

## Getting Started with Lean

In the exercises, you will write [Lean](https://github.com/leanprover/lean4) code. Lean is a functional programming language with a very expressive type system that makes it possible to state and check mathematical proofs. This project is built with [Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/), Lean's build system and package manager. We will work with [Mathlib](https://github.com/leanprover-community/mathlib4) and [CSLib](https://github.com/leanprover/cslib), two large bodies of existing formalization work in mathematics and computer science, respectively.

### Install Elan

[Elan](https://github.com/leanprover/elan) is a toolchain manager for Lean. Follow the official [installation guide](https://lean-lang.org/install/manual/) to set it up. Elan installs Lean and Lake for you.

### Clone the Repository

```bash
git clone https://github.com/sorrachai/FAA2026
cd FAA2026
```

### Download the Mathlib Cache and Build the Project

Building Mathlib from source takes hours, so save yourself the time and download a precompiled cache instead:

```bash
lake exe cache get
```

You only need to do this once per Lake project. To build the project, run:

```bash
lake build
```

### Set Up Your Editor

If you use VS Code, we strongly recommend installing the Lean extension. It shows the current goals and hypotheses in a side panel while you write proofs, and provides syntax highlighting, error messages, and code completion. Install it from the Extensions tab, or by running:

```bash
code --install-extension leanprover.lean4
```

If you use Neovim, the [lean.nvim](https://github.com/julian/lean.nvim) plugin offers similar functionality.

### Online Editor

If the setup above doesn't work for you, you can write Lean code in the [online editor](https://live.lean-lang.org/). If you run into trouble with the installation, please ask a TA during one of the first exercise sessions.

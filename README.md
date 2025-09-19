# Formal Sorting Verification in Lean4

Formal verification of sorting algorithms using Lean4.

## Aim

To define sorting algorithms in Lean4 and prove their correctness (sortedness and length preservation).

## Project Structure
```
formal-sorting-verification/
├── FormalSortingVerification/
│ └── Basic/
│ ├── Definitions.lean # Core definitions
│ └── Properties.lean # Theorems and proofs
├── lake/ # Lake build artifacts
├── notes/ # Personal learning notes
├── .gitignore
├── lakefile.toml
├── lean-toolchain
└── README.md
```

## Notes

- The `notes/` folder contains explanations and proofs in natural language.
- Focus is on insertion sort and merge sort, with proofs of correctness.

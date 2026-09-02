# Lane: ownership-invokers — the third artifact-ownership classification

<!-- plan-section: lane-status -->

**Your lane's block (`done`, ownership-invokers, 2026-09-02).**
`scripts/check-generated-artifact-ownership.py` is green again, and the arm
that makes it green is new rather than a widened exemption.

It was red because KNOWN demands that every script naming a GUARDED artifact
be classified, and `scripts/lane-merge-land.sh` names the frontier shape census
artifact in its `GENERATED` array. Neither category the remedy line offered was
honest: `runs` would EXECUTE a merge driver inside the ownership sandbox, and
`reads` is false for a script that redirects and stages (its decision procedure
is an AST scan that does not apply to bash at all). The script names the
artifact only to clear a merge conflict on it and stage it, and produces its
content by calling the OWNER.

`invokes` is that missing category, verified BY INSPECTION like `reads`: every
line REACHING the artifact's name must be a git staging line, and the owner's
path must appear in the script. Bindings are followed — the real script binds
the path into an array and stages the array's elements, so an arm judging only
the naming LINE would accept an array later used to copy over the file — and a
binding that itself writes (`P = open(path, "w")`) is judged rather than
exempted. Two further guards keep it from passing vacuously: a redirection
whose target is the artifact fails even on a line carrying a staging word, and
a classification under which no line is ever judged is refused.

Mutation, in an isolated snapshot (`scripts/tests/mutation_controls.py
artifact-ownership`, 25 mutants, exit 0, no survivors, nothing unmeasured): the
six guards each kill exactly one test. The seventh mutant — bindings are
FOLLOWED — kills four, and that is the arm's REACHABILITY rather than a guard:
every fixture that binds a name depends on it, including the real-tree control
whose script is the array shape. Removing it makes the arm judge the BINDING
line and refuse the real script, so the four deaths are over-firing, not a
shared blind spot.

A second red in the same controls came from the same landing and is fixed here:
`test_every_guarded_artifact_is_itself_a_candidate` asserted a universal that is
false for an artifact guarded with ONE writer whose producer is not named
`gen-*.py` — COVER's producer population structurally cannot see it, and need
not, since guarding is stronger than being a candidate and
`--update-candidates` omits guarded artifacts by design. The control now
asserts what it is for: that the derivation is not silently empty.

Next for whoever picks this up: the arm's staging list (`add`, `checkout`,
`restore`, `rm`, `stage`, `update-index`) is a closed literal, and a new git
subcommand that moves a file would be refused rather than misread — the safe
direction, but someone will have to extend it deliberately.

<!-- plan-section: landed-changes -->

| 2026-09-02 | `dd5b54b68` | `invokes`, the third artifact-ownership classification: an orchestrator may name a guarded artifact to STAGE it and must regenerate it by calling the owner, checked by inspection. Gate FAIL→PASS with no artifact changed; 25 mutants, exit 0. |

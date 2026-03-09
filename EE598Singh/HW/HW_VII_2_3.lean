/-
HW_VII_2_3.lean — EE598
Sukhman Singh

Instructions (interpreted from assignment):
- Part 2: get started on the Lean final project repo and document it.
- Part 3: read the assigned article and share thoughts.
- As with prior EE598 homework files, I restate the task in comments and
  place the written response directly in this Lean file.
- Lean code should compile with no errors.

Article:
Matthew Connelly, “A.I. Companies Are Eating Higher Education,”
New York Times, Feb. 12, 2026.
-/

import Mathlib

/-
============================================================
Part 2 — Get started
============================================================

Restatement of assignment:
- Start a new Lean project.
- Create a GitHub repo and share it with Eric.
- If public, include a LICENSE.md.
- Add a one-paragraph README.md describing the project.
- Make a TODO.md with achievable goals in order.
- As progress is made, update README and TODO.

What I have done:
- I created the project repo:
    poly-functors-ee598
- The repo is private, which is allowed by the assignment.
  Because it is private, a LICENSE.md is not required by the prompt.
- I added Eric on GitHub (account: klavins) as a collaborator.
- I added a README.md with a one-paragraph project description.
- I added a TODO.md with ordered milestones and have already updated it
  as the project evolved.

Project summary:
My EE598 final project formalizes polynomial functors (containers) in Lean 4.
I represent a polynomial by shapes and positions, define its semantics
as X ↦ Σ a, (B a → X), and formalize morphisms as dependent lenses.
The current development already includes the core container definition,
morphisms, a category instance, evaluation semantics, algebraic constructors
such as sums/products/composition, and bridges to Mathlib’s PFunctor.
The next stages focus on universal properties, monoidal structure, and one
larger theorem aligned with the book.

Current TODO status (summarized from TODO.md):
- repo/build sanity: done
- core containers + lenses: done
- evaluation as functor / semantics embedding: mostly done
- algebraic constructors: done
- universal properties in PolyC: done
- parallel product / symmetric monoidal structure: done
- composition product as monoidal structure: in progress
- one major theorem: planned
- polishing / examples / module comments: planned

Current TODO as seen in git raw:
# TODO — EE598 Poly Project (Book-Aligned)

## ✅ Milestone 0 — Repo + build sanity
- [x] Project builds locally with `lake build`
- [x] Repo is pushed to GitHub (private)
- [x] Eric added as collaborator and confirmed access

## ✅ Milestone 1 — Core containers + lenses (done)
- [x] `PolyC` as (shapes A, positions B)
- [x] semantics `eval : X ↦ Σ a, (B a → X)`
- [x] lens morphisms `Hom` + `map`
- [x] category instance `Category PolyC`

## ✅ Milestone 2 — Evaluation as functor + semantics embedding (mostly done)
- [x] `evalFunctor : Type ⥤ Type`
- [x] naturality lemma for `map`
- [x] `homToNatTrans` and `Sem : PolyC ⥤ (Type ⥤ Type)` (after Semantics file compiles)

## ✅ Milestone 3 — Algebraic constructors (done, but now formalize universal properties)
- [x] `sum`, `prod`, `composeObj` + evaluation equivalences

## ✅ Milestone 4 — Universal properties in PolyC (nontrivial, category-theoretic)
- [x] Prove `sum` is a coproduct in `PolyC` (explicit injections + UP)
- [x] Prove `prod` is a product in `PolyC` (explicit projections + UP)
- [x] Clean statements: `Hom (sum P Q) R ≃ Hom P R × Hom Q R`, etc.

## ✅ Milestone 5 — Parallel product ⊗ (Dirichlet product) + symmetric monoidal structure
- [x] Define `⊗` on objects and morphisms
- [x] Define unit polynomial `y`
- [x] Construct isomorphisms: left/right unitor, associator, braiding
- [x] Prove distributivity over sums: `(P + Q) ⊗ R ≅ (P ⊗ R) + (Q ⊗ R)` (or similar)

## Milestone 6 — Composition product ⊳ (monoidal structure from composition)
- [ ] Extend `composeObj` to a bifunctor on morphisms (hard part!)
- [ ] Construct associator/unitor isomorphisms for ⊳
- [ ] Show `eval` respects composition up to iso (already have object-level equivalence)

## Milestone 7 — pick ONE major theorem
- [ ] Option A: Cartesian closedness (exponentials) for Poly (book Thm 5.32 style)
- [ ] Option B: Equalizers / limits characterization (“positions limit, directions colimit”)

## Polishing / usability
- [ ] Reduce `import Mathlib` in Core to narrower imports (optional performance cleanup)
- [ ] Add `Poly/README.md` or module comments describing dependency graph
- [ ] Add a few runnable examples and sanity checks

Why this satisfies the assignment:
The assignment asked for a real Lean project with documentation and an ordered
plan, not a finished final result. I have already met the setup requirements
and moved beyond setup into actual formalization work, while keeping README
and TODO aligned with the current state of the project.
-/

/-
============================================================
Part 3 — Response to the article
============================================================

Restatement of assignment:
Read the article
“A.I. Companies Are Eating Higher Education”
and share my thoughts.

Response:

I think the article is strongest when it argues that universities should not
confuse rapid adoption with educational progress. That point matters. A tool
can be impressive, convenient, and even genuinely useful while still weakening
the habits that higher education is supposed to cultivate: close reading,
careful writing, sustained attention, and the ability to sit with confusion
long enough to actually understand something. The article is right to be wary
of universities outsourcing educational judgment to companies whose incentives
are not mainly pedagogical. If a platform’s goal is scale, market capture, or
dependency, then the university has to assume that those goals will sometimes
conflict with the slower and more demanding goal of developing human thought.

I also think the article is persuasive when it points to asymmetry. Universities
are told these are “partnerships,” but in practice the companies often control
the systems, the interfaces, the pricing, the usage incentives, and large parts
of the data environment. That is not a partnership of equals. The concern is
not just privacy or cheating in the narrow sense. It is governance. If the core
intellectual workflows of students start running through proprietary black boxes
that universities cannot meaningfully audit, then educational institutions are
slowly giving up control over the conditions under which thinking happens.

That said, I would not frame the problem as “A.I. versus human intelligence”
in a total sense. The issue is not that computational systems are inherently
anti-intellectual. The issue is that they can very easily become substitutes
for struggle instead of instruments for deeper struggle. Used badly, they let
students bypass the exact friction through which understanding is formed.
Used well, they can support experimentation, feedback, translation across
formalisms, rapid testing of examples, and exploration of alternative proofs
or viewpoints. So I do not think the right conclusion is blanket prohibition.
I think the right conclusion is that universities need much more intentional
norms about when A.I. is extending thought and when it is replacing it.

This matters directly to my own project in Lean. A formal proof assistant is
also a computational system, but the pedagogy is very different from passive
outsourcing. Lean can expose gaps in reasoning with extreme precision. It does
not simply reward polished language or plausible sounding arguments; it forces
definitions, types, dependencies, and proof steps to line up. In that sense,
formal methods can strengthen human intelligence instead of hollowing it out.
They externalize reasoning in a way that is inspectable and rigorous. So for me,
the important distinction is not “uses A.I.” versus “does not use A.I.” but
rather whether the technology preserves accountability to the structure of the
thought itself.

I also think the article is pointing at something broader about education in
2026: students are under enormous pressure, and companies know that. When tools
are marketed most aggressively at moments of stress, the risk is that education
gets reframed around relief from cognitive burden rather than formation through
intellectual effort. That is attractive in the short run, but it is dangerous
in the long run. A university should help students become more capable of doing
hard things, not just more capable of routing around them.

So overall, my view is close to the article’s central warning, but a little more
qualified in its conclusion. I agree that universities should resist dependency,
protect student work and data, and stop pretending that vendor enthusiasm is the
same thing as evidence of educational value. But I also think computational tools
can play a real constructive role when they are embedded inside disciplined forms
of inquiry. The standard should be whether the tool increases rigor, autonomy,
and depth of understanding. If it merely increases speed, convenience, or the
appearance of competence, then the article’s warning is exactly right.
-/

-- Dummy declaration so the file contains valid Lean code and compiles cleanly.
def HW_VII_2_3_Submitted : True := True.intro

example : HW_VII_2_3_Submitted = True.intro := rfl

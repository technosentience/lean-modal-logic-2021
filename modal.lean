import tactic

open classical
local attribute [instance] prop_decidable

universe u

inductive Formula : Type u
| absurd  : Formula
| var     : nat → Formula
| impl    : Formula → Formula → Formula
| conj    : Formula → Formula → Formula
| disj    : Formula → Formula → Formula
| nec     : Formula → Formula

axiom formulas_countable : encodable Formula
local attribute [instance] formulas_countable

notation  `⊥`     : 85 := Formula.absurd
prefix    `#`     : 65 := Formula.var
infixr    `→'`    : 55 := Formula.impl
notation  `¬'` x  : 60 := x →' ⊥
infixl    `∧'`    : 50 := Formula.conj
infixl    `∨'`    : 50 := Formula.disj
prefix    `□`     : 60 := Formula.nec
notation  `◇` x   : 60 := ¬' (□ (¬'x))

inductive proof (Ax: set Formula) : set Formula → set Formula
| ax  : ∀ A   : Formula, ∀ Γ : set Formula, A ∈ Ax → proof Γ A
| ctx : ∀ A   : Formula, ∀ Γ : set Formula, A ∈ Γ → proof Γ A
| mp  : ∀ A B : Formula, ∀ Γ : set Formula, proof Γ A → proof Γ (A →' B) → proof Γ B
| rn  : ∀ A   : Formula, ∀ Γ : set Formula, proof ∅ A → proof Γ □A

notation Γ `⊢[` A `]` f : 25 := proof A Γ f

structure Model : Type (u + 1) :=
mk :: (W : Type u) (r : W → W → Prop) (v : W → nat → Prop)

def loc_true (M : Model.{u}) : M.W → Formula → Prop
| w ⊥           := false
| w (#v)        := M.v w v
| w (f₁ →' f₂)  := loc_true w f₁ → loc_true w f₂
| w (f₁ ∧' f₂)  := loc_true w f₁ ∧ loc_true w f₂
| w (f₁ ∨' f₂)  := loc_true w f₁ ∨ loc_true w f₂
| w (□f)        := ∀ w' : M.W, M.r w w' → loc_true w' f

def loc_true_ctx (M : Model.{u}) (Γ : set Formula.{u}) (w : M.W) : Prop
  := ∀ f : Formula, f ∈ Γ → loc_true M w f

def models (M : set Model.{u}) (Γ : set Formula.{u}) (f : Formula.{u}) : Prop
  := ∀ m : Model, m ∈ M →
     ∀ w : m.W, loc_true_ctx m Γ w → loc_true m w f

notation Γ `⊨[` M `]` f : 25 := models M Γ f

def sound (A : set Formula.{u}) (M : set Model.{u}) : Prop
  :=  ∀ Γ : set Formula.{u}, ∀ f : Formula.{u},
      (Γ ⊢[A] f) → (Γ ⊨[M] f)

def complete (A : set Formula.{u}) (M : set Model.{u}) : Prop
  :=  ∀ Γ : set Formula.{u}, ∀ f : Formula.{u},
      (Γ ⊨[M] f) → (Γ ⊢[A] f)

inductive AxiomPC : set Formula
| implIntro   : ∀ A B   : Formula, AxiomPC $ A →' B →' A
| implChain   : ∀ A B C : Formula, AxiomPC $ (A →' B →' C) →' (A →' B) →' A →' C
| andIntro    : ∀ A B   : Formula, AxiomPC $ A →' B →' (A ∧' B)
| andElimL    : ∀ A B   : Formula, AxiomPC $ (A ∧' B) →' A
| andElimR    : ∀ A B   : Formula, AxiomPC $ (A ∧' B) →' B
| orIntroL    : ∀ A B   : Formula, AxiomPC $ A →' (A ∨' B)
| orIntroR    : ∀ A B   : Formula, AxiomPC $ B →' (A ∨' B)
| orElim      : ∀ A B C : Formula, AxiomPC $ (A →' C) →' (B →' C) →' (A ∨' B) →' C
| absurdElim  : ∀ A     : Formula, AxiomPC $ ⊥ →' A
| lem         : ∀ A     : Formula, AxiomPC $ A ∨' ¬' A

notation Γ `⊢ₚ` f : 25 := Γ ⊢[AxiomPC] f

inductive AxiomS5 : set Formula
| prop  : ∀ A   : Formula, A ∈ AxiomPC → AxiomS5 A
| axK   : ∀ A B : Formula, AxiomS5 $ □(A →' B) →' □A →' □B
| ref   : ∀ A   : Formula, AxiomS5 $ □A →' A
| sym   : ∀ A   : Formula, AxiomS5 $ A →' □◇A
| tran  : ∀ A   : Formula, AxiomS5 $ □A →' □□A

notation Γ `⊢₅` f : 25 := Γ ⊢[AxiomS5] f

def ModelS5 : set Model.{u} := λ M, equivalence M.r

notation Γ `⊨₅` f : 25 := Γ ⊨[ModelS5] f

theorem S5_sound : sound AxiomS5 ModelS5 :=
begin
  intros  context
          formula
          prf
          model
          rel_equiv
          world
          loc_ctx_truth,

  induction prf with
    _ _ in_ax generalizing world,

  -- automatically solve prop, axK, mp cases
  cases in_ax with _ prf',
  cases prf',
  repeat { finish [loc_true] }, 

  case ref : {
    intros boxA,
    exact boxA world (rel_equiv.1 world),
  },

  case sym : {
    intros A w' rw' h,
    exact h world (rel_equiv.2.1 rw') A,
  },

  case tran : {
    intros boxA w' rw' w'' rw'',
    exact boxA w'' (rel_equiv.2.2 rw' rw''),
  },

  case ctx : _ _ in_ctx {
    exact loc_ctx_truth _ in_ctx,
  },

  case rn : _ _ _ ih {
    intros w' _,
    apply ih,
    intros _ f,
    cases f,
  },
end

lemma proof_mp_ctx (A : set Formula) (Γ : set Formula) (f₁ f₂ : Formula)
  : f₁ ∈ Γ → (f₁ →' f₂) ∈ Γ → (Γ ⊢[A] f₂) :=
begin
  intros h₁ h₂,
  have h₃ : (Γ ⊢[A] f₁) := proof.ctx _ _ h₁,
  have h₄ : (Γ ⊢[A] (f₁ →' f₂)) := proof.ctx _ _ h₂,
  have h₅ := proof.mp _ _ _ h₃ h₄,
  assumption,
end

lemma proof_subset (A : set Formula) (Γ Γ' : set Formula) (f : Formula)
  : Γ ⊆ Γ' → (Γ ⊢[A] f) → (Γ' ⊢[A] f) :=
begin
  intros h₁ h₂,
  induction h₂,

  case ax : {
    apply proof.ax,
    assumption,
  },

  case ctx : {
    apply proof.ctx,
    tauto,
  },

  case mp : _ _ _ _ _ ih₁ ih₂ {
    have h₂ := ih₁ h₁,
    have h₃ := ih₂ h₁,
    exact proof.mp _ _ _ h₂ h₃,  
  },

  case rn : {
    apply proof.rn,
    assumption,
  },
end

lemma lift_subset (A₁ A₂ : set Formula) (as : A₁ ⊆ A₂) (Γ : set Formula)
  (f : Formula) : (Γ ⊢[A₁] f) → (Γ ⊢[A₂] f) :=
begin
  intro prf,
  induction prf,

  case proof.ax {
    apply proof.ax,
    apply as,
    assumption,
  },

  case proof.ctx {
    apply proof.ctx,
    assumption,
  },

  case proof.mp {
    apply proof.mp,
    assumption,
    assumption,
  },

  case proof.rn {
    apply proof.rn,
    assumption,
  },
end

lemma lift_S5 (Γ : set Formula) (f : Formula)
  : (Γ ⊢ₚ f) → (Γ ⊢₅ f) := lift_subset AxiomPC AxiomS5 (AxiomS5.prop) Γ f

lemma append_PC' (A : set Formula) (pc : AxiomPC ⊆ A) (Γ : set Formula)
  (f : Formula) (g : Formula) (h : Γ ⊢[A] g) : Γ ⊢[A] (f →' g) :=
begin
  have h₁ : (Γ ⊢[A] (g →' f →' g)),
  apply proof.ax,
  apply pc,
  apply AxiomPC.implIntro,

  exact proof.mp _ _ _ h h₁,
end

lemma append_PC (Γ : set Formula) (f : Formula) (g : Formula) (h : Γ ⊢ₚ g)
  : Γ ⊢ₚ (f →' g) := append_PC' AxiomPC (by refl) _ _ _ h

lemma append_S5 (Γ : set Formula) (f : Formula) (g : Formula) (h : Γ ⊢₅ g)
  : Γ ⊢₅ (f →' g) := append_PC' AxiomS5 (AxiomS5.prop) _ _ _ h

lemma refl_PC (Γ : set Formula) (f : Formula) : Γ ⊢ₚ (f →' f) :=
begin
  have h₁ : (Γ ⊢ₚ ((f →' (f →' f) →' f) →' (f →' f →' f) →' (f →' f))),
  apply proof.ax,
  apply AxiomPC.implChain,

  have h₂ : (Γ ⊢ₚ (f →' (f →' f) →' f)),
  apply proof.ax,
  apply AxiomPC.implIntro,

  have h₃ : (Γ ⊢ₚ (f →' f →' f)),
  apply proof.ax,
  apply AxiomPC.implIntro,

  have h₄ := proof.mp _ _ _ h₂ h₁,
  have h₅ := proof.mp _ _ _ h₃ h₄,
  exact h₅,
end

lemma refl_S5 (Γ : set Formula) (f : Formula) : Γ ⊢₅ (f →' f)
  := lift_S5 _ _ $ refl_PC _ _

theorem deduction_PC' (A : set Formula) (pc : AxiomPC ⊆ A)
  (Γ : set Formula) (f : Formula) (g : Formula)
  : (insert f Γ ⊢[A] g) ↔ (Γ ⊢[A] (f →' g)) :=
begin
  split,

  generalize eq : insert f Γ = Γ',

  intro prf,
  induction prf,

  case proof.ax : A' _ ax {
    apply append_PC',
    assumption,

    apply proof.ax,
    assumption,
  },

  case proof.ctx : A' _ ctx {
    rw [←eq] at ctx,
    cases ctx,

    case or.inl : {
      rw ctx,
      apply lift_subset AxiomPC A pc,
      apply refl_PC,
    },

    case or.inr : {
      apply append_PC',
      assumption,

      apply proof.ctx,
      assumption,
    },
  },

  case proof.mp : A' B' _ _ _ ih₁ ih₂ {
    have h₁ : (Γ ⊢[A] ((f →' A' →' B') →' (f →' A') →' f →' B')),
    apply proof.ax,
    apply pc,
    apply AxiomPC.implChain,

    have h₂ := proof.mp _ _ _ (ih₂ eq) h₁,
    have h₃ := proof.mp _ _ _ (ih₁ eq) h₂,
    assumption,
  },

  case proof.rn : A _ h₁ _ {
    apply append_PC',
    assumption,

    apply proof.rn,
    assumption,
  },

  intro h₁,
  have h₂ : (insert f Γ ⊢[A] f) := proof.ctx _ _ (by finish),
  have h₃ : (insert f Γ ⊢[A] (f →' g)) :=
    proof_subset _ _ _ _ (by finish) h₁,
  have h₄ := proof.mp _ _ _ h₂ h₃,
  assumption,
end

theorem deduction_PC (Γ : set Formula) (f: Formula) (g: Formula)
  : (insert f Γ ⊢ₚ g) ↔ (Γ ⊢ₚ (f →' g))
  := deduction_PC' AxiomPC (by refl) _ _ _

theorem deduction_S5 (Γ : set Formula) (f: Formula) (g: Formula)
  : (insert f Γ ⊢₅ g) ↔ (Γ ⊢₅ (f →' g))
  := deduction_PC' AxiomS5 AxiomS5.prop _ _ _

lemma dneg_intro_PC (Γ : set Formula) (f : Formula) 
  : (Γ ⊢ₚ (f →' ¬' ¬'f)) :=
begin
  rw [←deduction_PC],
  rw [←deduction_PC],
  set Γ' := insert (f→'⊥) (insert f Γ),

  have h₁ : (Γ' ⊢ₚ f) := proof.ctx _ _ (by finish),
  have h₂ : (Γ' ⊢ₚ (f →' ⊥)) := proof.ctx _ _ (by finish),
  exact proof.mp _ _ _ h₁ h₂, 
end

lemma dneg_elim_PC (Γ : set Formula) (f : Formula)
  : (Γ ⊢ₚ (¬' ¬' f →' f)) :=
begin
  rw [←deduction_PC],
  set Γ' := insert ((f→'⊥)→'⊥) Γ,

  have h₁ : (Γ' ⊢ₚ (f ∨' ¬' f)),
  apply proof.ax,
  apply AxiomPC.lem,

  have h₂ : (Γ' ⊢ₚ (⊥ →' f)),
  apply proof.ax,
  apply AxiomPC.absurdElim,

  have h₃ : (Γ' ⊢ₚ (¬'f →' ⊥ →' f) →' (¬' ¬' f) →' (¬' f) →' f),
  apply proof.ax,
  apply AxiomPC.implChain,

  have h₄ : (Γ' ⊢ₚ (¬'f →' ⊥ →' f)) := append_PC _ _ _ h₂,

  have h₅ : (Γ' ⊢ₚ (¬' ¬' f) →' (¬'f) →' f) := proof.mp _ _ _ h₄ h₃,

  have h₆ : (Γ' ⊢ₚ (¬' ¬' f)) := proof.ctx _ _ (by finish),

  have h₇ : (Γ' ⊢ₚ (¬' f →' f)) := proof.mp _ _ _ h₆ h₅,

  have h₈ : (Γ' ⊢ₚ (f →' f) →' (¬' f →' f) →' (f ∨' ¬' f) →' f),
  apply proof.ax,
  apply AxiomPC.orElim,

  have h₉ : (Γ' ⊢ₚ (f →' f)) := refl_PC _ _,

  have h₁₀ : (Γ' ⊢ₚ (¬' f →' f) →' (f ∨' ¬' f) →' f) := proof.mp _ _ _ h₉ h₈,

  have h₁₁ : (Γ' ⊢ₚ ((f ∨' ¬' f) →' f)) := proof.mp _ _ _ h₇ h₁₀,

  have h₁₂ : (Γ' ⊢ₚ f) := proof.mp _ _ _ h₁ h₁₁,

  assumption,
end

lemma contrapose_PC' (Γ : set Formula) (f g : Formula)
  : Γ ⊢ₚ ((f →' g) →' (¬'g →' ¬' f)) :=
begin
  rw [←deduction_PC],
  rw [←deduction_PC],
  rw [←deduction_PC],
  set Γ' := insert f (insert (g→'⊥) (insert (f→' g) Γ)),

  have h₁ : (Γ' ⊢ₚ f) := proof.ctx _ _ (by finish),
  have h₂ : (Γ' ⊢ₚ (f →' g)) := proof.ctx _ _ (by finish),
  have h₃ : (Γ' ⊢ₚ g) := proof.mp _ _ _ h₁ h₂,
  have h₄ : (Γ' ⊢ₚ (g →' ⊥)) := proof.ctx _ _ (by finish),
  have h₅ : (Γ' ⊢ₚ ⊥) := proof.mp _ _ _ h₃ h₄,

  assumption,
end

lemma contrapose_PC (Γ : set Formula) (f g : Formula)
  : (Γ ⊢ₚ (f →' g)) → (Γ ⊢ₚ (¬' g →' ¬' f)) :=
begin
  intro h₁,
  have h₂ := contrapose_PC' Γ f g,
  exact proof.mp _ _ _ h₁ h₂,
end

lemma contrapose_S5 (Γ : set Formula) (f g : Formula)
  : (Γ ⊢₅ (f →' g)) → (Γ ⊢₅ (¬' g →' ¬' f)) :=
begin
  intro h₁,
  have h₂ := lift_S5 _ _ (contrapose_PC' Γ f g),
  exact proof.mp _ _ _ h₁ h₂,
end


lemma nec_k (f g : Formula) : (∅ ⊢₅ (f →' g)) → (∅ ⊢₅ (□f →' □g)) :=
begin
  intro h₁,

  have h₂ : (∅ ⊢₅ □(f →' g)),
  apply proof.rn,
  assumption,

  have h₃ : (∅ ⊢₅ (□(f →' g) →' □f →' □g)),
  apply proof.ax,
  apply AxiomS5.axK,

  have h₄ : (∅ ⊢₅ (□f →' □g)) := proof.mp _ _ _ h₂ h₃, 
  assumption,
end

lemma S5_sym_alt (Γ : set Formula) (f : Formula) : Γ ⊢₅ (◇ □ f →' f) :=
begin
  rw [←deduction_S5],
  set Γ' := insert (□(□f→'⊥)→'⊥) Γ,

  have h₁ : (Γ' ⊢₅ (¬' f →' □ ◇ ¬' f)),
  apply proof.ax,
  apply AxiomS5.sym,

  have h₂ := contrapose_S5 _ _ _ h₁,

  have h₃ : (∅ ⊢₅ (f →' ¬' ¬' f)),
  apply lift_S5,
  apply dneg_intro_PC,

  have h₄ := nec_k _ _ h₃,
  have h₅ := contrapose_S5 _ _ _ h₄,
  have h₆ := nec_k _ _ h₅,
  have h₇ := contrapose_S5 _ _ _ h₆,
  have h₈ := proof_subset AxiomS5 ∅ Γ' _ (by finish) h₇,

  have h₉ : (Γ' ⊢₅ (□(□f→'⊥)→'⊥)) := proof.ctx _ _ (by finish), 
  have h₁₀ := proof.mp _ _ _ h₉ h₈,
  have h₁₁ := proof.mp _ _ _ h₁₀ h₂,
  
  have h₁₂ : (Γ' ⊢₅ (¬' ¬'f →' f)),
  apply lift_S5,
  apply dneg_elim_PC,

  have h₁₃ := proof.mp _ _ _ h₁₁ h₁₂,
  assumption,
end

def consistent (A : set Formula) (Γ : set Formula) : Prop
  := ¬(Γ ⊢[A] ⊥)

def cons_ext (A : set Formula) (Γ : set Formula) (f : Formula) : set Formula
  := if consistent A (Γ ∪ {f}) then Γ ∪ {f} else Γ ∪ {¬'f}

def cons_ext_nth (A : set Formula) (Γ : set Formula) (n : nat) : set Formula
  := 
     match encodable.decode Formula n with
     | none := Γ
     | some f := cons_ext A Γ f
     end

def cons_ext_chain (A : set Formula) (Γ : set Formula) : nat → set Formula
| 0 := Γ
| (n + 1) := cons_ext_nth A (cons_ext_chain n) n

def cons_ext_max (A : set Formula) (Γ : set Formula) : set Formula
  := ⋃ n : nat, cons_ext_chain A Γ n

lemma cons_ext_sub (A: set Formula) (Γ : set Formula) (f : Formula)
  : Γ ⊆ cons_ext A Γ f :=
begin
  simp [cons_ext],
  split_ifs,
  finish,
  finish,
end

lemma cons_ext_nth_sub (A: set Formula) (Γ : set Formula) (n : nat)
  : Γ ⊆ cons_ext_nth A Γ n :=
begin
  simp [cons_ext_nth],
  cases encodable.decode Formula n,
  finish,
  finish [cons_ext_nth, cons_ext_sub],
end

lemma cons_ext_chain_sub₁ (A : set Formula) (Γ : set Formula) (n : nat)
  : cons_ext_chain A Γ n ⊆ cons_ext_chain A Γ (n + 1) :=
  by finish [cons_ext_chain, cons_ext_nth_sub]

lemma cons_ext_chain_sub₂ (A : set Formula) (Γ : set Formula) (m n : nat)
  : m ≤ n → cons_ext_chain A Γ m ⊆ cons_ext_chain A Γ n := 
begin
  intro h₁,
  cases nat.le.dest h₁ with n' h₂,
  rw [←h₂] at *,
  clear h₂ h₁ n,

  induction n',
  refl,
  exact set.subset.trans n'_ih (cons_ext_chain_sub₁ _ _ _),
end

lemma cons_ext_max_sub (A : set Formula) (Γ : set Formula)
  : Γ ⊆ cons_ext_max A Γ := set.subset_Union (cons_ext_chain A Γ) 0

lemma cons_ext_cons (Γ : set Formula) (f : Formula)
  (h : consistent AxiomS5 Γ) : consistent AxiomS5 (cons_ext AxiomS5 Γ f) :=
begin
  by_cases h₁ : consistent AxiomS5 (Γ ∪ {f}),
  finish [cons_ext],

  simp [cons_ext, consistent] at *,
  split_ifs,
  by_contradiction h₂,

  have h₃ : ¬consistent AxiomS5 Γ,  
  simp [consistent],
  
  have h₄ : (Γ ⊢[AxiomS5] (f ∨' ¬'f)),
  apply proof.ax,
  apply AxiomS5.prop,
  apply AxiomPC.lem,

  have h₅ : (Γ ⊢[AxiomS5] ((f →' ⊥) →' (¬' f →' ⊥) →' (f ∨' ¬' f) →' ⊥)),
  apply proof.ax,
  apply AxiomS5.prop,
  apply AxiomPC.orElim,

  have h₆ := (deduction_S5 Γ f ⊥).mp h₁,
  have h₇ := (deduction_S5 Γ (¬'f) ⊥).mp h₂,

  have h₈ := proof.mp _ _ Γ h₆ h₅,
  have h₉ := proof.mp _ _ Γ h₇ h₈,
  have h₁₀ := proof.mp _ _ Γ h₄ h₉,
  exact h₁₀,

  contradiction,
end

lemma cons_ext_nth_cons (Γ : set Formula) (n : nat)
  (h : consistent AxiomS5 Γ) : consistent AxiomS5 (cons_ext_nth AxiomS5 Γ n) :=
begin
  simp [cons_ext_nth],
  cases encodable.decode Formula n,
  finish,
  finish [cons_ext_nth, cons_ext_cons], 
end

lemma cons_ext_chain_cons (Γ : set Formula) (n : nat)
  (h : consistent AxiomS5 Γ) : consistent AxiomS5 (cons_ext_chain AxiomS5 Γ n) :=
begin
  induction n,
  finish,
  finish [cons_ext_chain, cons_ext_nth_cons],
end

theorem finite_derivation (A : set Formula) (Γ : set Formula) (f : Formula)
  : ((cons_ext_max A Γ) ⊢[A] f) → ∃ n : ℕ, ((cons_ext_chain A Γ n) ⊢[A] f) :=
begin
  generalize eq : cons_ext_max A Γ = Γ',
  intro h,
  induction h,

  case ax : {
    use 0,
    apply proof.ax,
    assumption,
  },

  case ctx : _ _ ctx {    
    subst eq,
    simp [cons_ext_max] at ctx,
    cases ctx with n d,
    use n,
    apply proof.ctx,
    assumption,  
  },
  
  case mp : A' B' _ _ _ ih₁ ih₂ {
    subst eq,
    cases ih₁ (by refl) with n₁ d₁,
    cases ih₂ (by refl) with n₂ d₂,

    use max n₁ n₂,
    apply proof.mp A' B',
  
    apply proof_subset _ (cons_ext_chain A Γ n₁),
    apply cons_ext_chain_sub₂,
    finish,
    assumption,

    apply proof_subset _ (cons_ext_chain A Γ n₂),
    apply cons_ext_chain_sub₂,
    finish,
    assumption,
  },

  case rn : {
    use 0,
    apply proof.rn,
    assumption,
  },
end

lemma cons_ext_max_cons (Γ : set Formula) (h₁ : consistent AxiomS5 Γ)
  : consistent AxiomS5 (cons_ext_max AxiomS5 Γ) :=
begin
  by_contradiction h₂,
  simp [consistent] at *,
  cases finite_derivation _ _ _ h₂ with n h₃,
  have h₄ := cons_ext_chain_cons _ n h₁, 
  contradiction,
end

lemma cons_ext_max_equicons (Γ : set Formula)
  : consistent AxiomS5 Γ ↔ consistent AxiomS5 (cons_ext_max AxiomS5 Γ) :=
begin
  split,
  apply cons_ext_max_cons,

  contrapose,
  simp [consistent],
  apply proof_subset,
  apply cons_ext_max_sub,
end

lemma cons_ext_max_em (A : set Formula) (Γ : set Formula) (f : Formula)
  : f ∈ cons_ext_max A Γ ∨ (¬'f) ∈ cons_ext_max A Γ :=
begin
  set n := encodable.encode f,
  have h₁ : cons_ext_chain A Γ (n + 1) ⊆ cons_ext_max A Γ := 
    by simp [cons_ext_max, set.subset_Union],
  
  simp [cons_ext_chain, cons_ext_nth, cons_ext] at *,
  split_ifs at *,

  left,
  apply h₁,
  finish,  

  right,
  apply h₁,
  finish,
end

theorem cons_ext_max_closed (Γ : set Formula) (f : Formula) 
  (h₁ : consistent AxiomS5 Γ) (h₂ : (cons_ext_max AxiomS5 Γ) ⊢[AxiomS5] f)
  : f ∈ (cons_ext_max AxiomS5 Γ) :=
begin
  cases cons_ext_max_em AxiomS5 Γ f with _ h₃,
  assumption,
  
  have h₄ := proof.ctx _ _ h₃,
  have h₅ := proof.mp _ _ _ h₂ h₄,
  have h₆ := cons_ext_max_cons _ h₁,
  contradiction,
end

lemma cons_ext_max_der_equiv (Γ : set Formula) (f : Formula) (h : consistent AxiomS5 Γ)
  : (cons_ext_max AxiomS5 Γ ⊢₅ f) ↔ f ∈ cons_ext_max AxiomS5 Γ :=
begin
  split,
  exact cons_ext_max_closed _ _ h, 
  exact proof.ctx _ _,
end

inductive CanonS5_W : set (set Formula.{u})
| mk : ∀ Γ : set Formula, consistent AxiomS5 Γ → CanonS5_W (cons_ext_max AxiomS5 Γ)

def v_mem (w : CanonS5_W.{u}) (f : Formula.{u}) : Prop := f ∈ (↑w : set Formula.{u})

def unbox (w : set Formula.{u}) : set Formula.{u} := { f | □f ∈ w } 

def CanonS5_R (w₁ w₂ : CanonS5_W.{u}) : Prop :=
  unbox (w₁ : set Formula.{u}) ⊆ (w₂ : set Formula.{u})

def CanonS5_v (w : CanonS5_W.{u}) (n : nat) : Prop := v_mem w #n

lemma v_mem_der_equiv (w : CanonS5_W.{u}) (f : Formula.{u})
  : (v_mem w f) ↔ ((w : set Formula.{u}) ⊢₅ f) :=
begin
  cases w, induction w_property,
  simp [v_mem],
  rw [cons_ext_max_der_equiv],
  assumption,
end

lemma v_mem_em (w : CanonS5_W.{u}) (f : Formula.{u})
  : v_mem w f ∨ v_mem w ¬'f :=
begin
  cases w, induction w_property,
  apply cons_ext_max_em,
end

lemma CanonS5_R_refl : reflexive CanonS5_R :=
begin
  intros w₁ f h₁,
  
  cases w₁,
  simp [unbox] at *,
  induction w₁_property,

  apply cons_ext_max_closed,
  tauto,

  rw cons_ext_max_equicons at *,
  have h₂ : (_ ⊢₅ _) := proof.ctx _ _ h₁,  
  have h₃ := proof.ax _ (cons_ext_max AxiomS5 w₁_property_Γ) (AxiomS5.ref f),

  exact proof.mp _ _ _ h₂ h₃,
end

lemma CanonS5_R_sym : symmetric CanonS5_R :=
begin
  intros w₁ w₂ h₁ f h₂,

  cases w₁,
  cases w₂,
  simp [CanonS5_R] at *,
  simp [unbox] at *,
  induction w₁_property,
  induction w₂_property,
  

  cases cons_ext_max_em AxiomS5 w₁_property_Γ □¬'□ f with h₃ h₃;
  rw [←cons_ext_max_der_equiv] at *;
  set Γ₁ := cons_ext_max AxiomS5 w₁_property_Γ,
  set Γ₂ := cons_ext_max AxiomS5 w₂_property_Γ,

  have h₄ := h₁ ((cons_ext_max_der_equiv _ _ _).mp h₃),
  rw [←cons_ext_max_der_equiv] at *,
  repeat { tauto },


  have h₅ := proof.mp _ _ _ h₂ h₄,
  exfalso,

  have h₇ := cons_ext_max_cons _ w₂_property_ᾰ,
  contradiction,

  have h₄ := S5_sym_alt Γ₁ f,
  have h₅ := proof.mp _ _ _ h₃ h₄,
  
  assumption,
end

lemma CanonS5_R_trans : transitive CanonS5_R :=
begin
  intros w₁ w₂ w₃ h₁ h₂ f h₃,

  cases w₁,
  cases w₂,
  cases w₃,
  induction w₁_property,
  induction w₂_property,
  induction w₃_property,
  simp [CanonS5_R, v_mem, unbox] at *,
  rw [←cons_ext_max_der_equiv] at h₃,

  have h₄ : (cons_ext_max AxiomS5 w₁_property_Γ ⊢₅ (□f →' □□f)),
  apply proof.ax,
  apply AxiomS5.tran,

  have h₅ := proof.mp _ _ _ h₃ h₄,
  rw [cons_ext_max_der_equiv] at h₅,
  apply h₂,
  apply h₁,

  repeat {tauto},
end

def CanonS5 : Model.{u} := { W := CanonS5_W.{u}, r := CanonS5_R.{u}, v := CanonS5_v.{u}}

lemma CanonS5_models : ModelS5 CanonS5 := 
  ⟨CanonS5_R_refl, ⟨CanonS5_R_sym, CanonS5_R_trans⟩⟩

lemma unbox_deriv (w : CanonS5_W.{u}) (f : Formula.{u})
  : (unbox (↑w : set Formula.{u}) ⊢₅ f) → v_mem w (□f) :=
begin
  generalize eq : unbox (↑w : set Formula.{u}) = Γ',
  intro prf,
  induction prf,

  case ax {
    rw [v_mem_der_equiv],
    apply proof.rn,
    apply proof.ax,
    assumption,
  },

  case ctx : A _ prf_A {
    rw [v_mem_der_equiv],
    apply proof.ctx,
    subst eq,
    simp [unbox] at *,
    rw [←v_mem] at *,
    rw [v_mem_der_equiv] at *,
    assumption,
 },

  case mp : A B _ _ _ ihA ihB {
    subst eq,
    simp at *,
    rw [v_mem_der_equiv] at *,
    
    have h₁ : ((w : set Formula.{u}) ⊢₅ (□(A →' B) →' □A →' □B)),
    apply proof.ax,
    apply AxiomS5.axK,

    have h₂ := proof.mp _ _ _ ihB h₁,
    have h₃ := proof.mp _ _ _ ihA h₂,
    assumption,
  },

  case rn {
    rw [v_mem_der_equiv],
    apply proof.rn,
    apply proof.rn,
    assumption,
  },
end

lemma CanonS5_v_equiv (w : CanonS5_W.{u}) (f : Formula.{u}) :
  v_mem w f ↔ loc_true CanonS5 w f :=
begin
  induction f generalizing w,

  case absurd {
    simp [v_mem_der_equiv, loc_true],
    cases w, induction w_property,
    apply cons_ext_max_cons,
    assumption,
  },

  case var {
    tauto,
  },

  case impl : A B ih₁ ih₂ {
    specialize ih₁ w,
    specialize ih₂ w,

    simp [loc_true] at *,
    rw [←ih₁, ←ih₂] at *,
    simp [v_mem_der_equiv] at *,

    split,

    intros h₁ h₂,
    exact proof.mp _ _ _ h₂ h₁,

    intro h₁,
    
    cases v_mem_em w A with h₂ h₂;
    simp [v_mem_der_equiv] at *,
    apply append_S5,
    tauto,

    rw [←deduction_S5] at h₂,
    rw [←deduction_S5],

    have h₃ : (insert A (w : set Formula.{u}) ⊢₅ (⊥ →' B)),
    apply proof.ax,
    apply AxiomS5.prop,
    apply AxiomPC.absurdElim,       

    exact proof.mp _ _ _ h₂ h₃,
  },


  case conj : A B ih₁ ih₂ {
    specialize ih₁ w,
    specialize ih₂ w,

    simp [v_mem_der_equiv, loc_true] at *,
    split,

    intro h₁,
    
    have h₂ : ((w : set Formula.{u}) ⊢₅ ((A ∧' B) →' A)),
    apply proof.ax,
    apply AxiomS5.prop,
    apply AxiomPC.andElimL,

    have h₃ : ((w : set Formula.{u}) ⊢₅ ((A ∧' B) →' B)),
    apply proof.ax,
    apply AxiomS5.prop,
    apply AxiomPC.andElimR,

    split,
    
    rw ←ih₁,
    exact proof.mp _ _ _ h₁ h₂,

    rw ←ih₂,
    exact proof.mp _ _ _ h₁ h₃,

    rw [←ih₁, ←ih₂],
    intro h₁,

    have h₂ : ((w : set Formula.{u}) ⊢₅ (A →' B →' (A ∧' B))),
    apply proof.ax,
    apply AxiomS5.prop,
    apply AxiomPC.andIntro,

    have h₃ := proof.mp _ _ _ h₁.1 h₂,
    have h₄ := proof.mp _ _ _ h₁.2 h₃,
    assumption,
  },

  case disj : A B ih₁ ih₂ {
    specialize ih₁ w,
    specialize ih₂ w,

    simp [loc_true] at *,
    rw [←ih₁, ←ih₂] at *,
    simp [v_mem_der_equiv] at *,
    split,

    intro h₁,

    cases v_mem_em w A with h₂ h₂,
    left,
    simp [v_mem_der_equiv] at *,
    assumption,

    cases v_mem_em w B with h₃ h₃,
    right,
    simp [v_mem_der_equiv] at *,
    assumption,
     
    simp [v_mem_der_equiv] at *,
    exfalso,

    have h₄ : ((w : set Formula.{u}) ⊢₅ (¬' A →' ¬' B →' ¬'(A ∨' B))),
    apply proof.ax,
    apply AxiomS5.prop,
    apply AxiomPC.orElim,

    have h₅ := proof.mp _ _ _ h₂ h₄,
    have h₆ := proof.mp _ _ _ h₃ h₅,
    have h₇ := proof.mp _ _ _ h₁ h₆,
    
    cases w, induction w_property,
    have h₈ := cons_ext_max_cons _ w_property_ᾰ,
    contradiction,

    intro h₁,
    cases h₁,
    
    have h₂ : ((w : set Formula.{u}) ⊢₅ (A →' (A ∨' B))),
    apply proof.ax,
    apply AxiomS5.prop,
    apply AxiomPC.orIntroL,
    exact proof.mp _ _ _ h₁ h₂,

    have h₂ : ((w : set Formula.{u}) ⊢₅ (B →' (A ∨' B))),
    apply proof.ax,
    apply AxiomS5.prop,
    apply AxiomPC.orIntroR,
    exact proof.mp _ _ _ h₁ h₂,
  },

  case nec : A ih {
    split,

    intros h₁ w' acc,
    rw [←ih],
    apply acc,
    simp [*, v_mem, unbox] at *,

    intro h₁,
    cases v_mem_em w □A with h₂ h₂,
    assumption,

    exfalso,
    set Γ' : set Formula.{u} := 
      insert (¬'A) (unbox (w : set Formula.{u})) with eq,

    have h₃ : consistent AxiomS5 Γ' := 
      begin
        intro h₃,
        simp [eq] at h₃,    
        simp [deduction_S5] at h₃, 

        have h₄ := unbox_deriv _ _ h₃,
        rw [v_mem_der_equiv] at h₂,
        rw [v_mem_der_equiv] at h₄,

        have h₅ : ((w : set Formula.{u}) ⊢₅ □(¬' ¬' A →' A)),
        apply proof.rn,
        apply lift_S5,
        apply dneg_elim_PC,

        have h₆ : ((w : set Formula.{u}) ⊢₅ (□(¬' ¬' A →' A)) →' □ ¬' ¬' A →' □ A),
        apply proof.ax,
        apply AxiomS5.axK,
        
        have h₇ := proof.mp _ _ _ h₅ h₆,
        have h₈ := proof.mp _ _ _ h₄ h₇,
        have h₉ := proof.mp _ _ _ h₈ h₂,

        cases w, induction w_property,
        apply cons_ext_max_cons,
        assumption,
        assumption,
      end,

    set w_mem := CanonS5_W.mk.{u} Γ' h₃,

    simp [loc_true] at h₁,
    specialize h₁ ⟨cons_ext_max AxiomS5 Γ', w_mem⟩,

    have h₄ : CanonS5.r w ⟨cons_ext_max AxiomS5 Γ', w_mem⟩,
    intros f h₅,
    apply cons_ext_max_sub,
    finish,

    specialize h₁ h₄,
    rw [←ih] at h₁,

    simp [v_mem_der_equiv] at *,

    have h₅ : (cons_ext_max AxiomS5 Γ' ⊢₅ ¬' A),
    apply proof.ctx,
    apply cons_ext_max_sub,
    finish,

    have h₆ := proof.mp _ _ _ h₁ h₅,
    have h₇ := cons_ext_max_cons _ h₃,
    contradiction,
  },
end

theorem S5_complete : complete AxiomS5.{u} ModelS5.{u} :=
begin
  simp [complete],
  intros Γ f,

  set Γ' := cons_ext_max AxiomS5 (Γ ∪ {¬' f}),

  by_cases h₁ : consistent AxiomS5 (Γ ∪ {¬' f}),
  contrapose,

  intros prf mdl,

  have h₂ : CanonS5_W Γ',
  fconstructor,
  assumption,

  specialize mdl CanonS5 CanonS5_models ⟨Γ', h₂⟩ _,
  rw [←CanonS5_v_equiv] at mdl,
  simp [v_mem] at mdl,
  rw [←cons_ext_max_der_equiv] at mdl,
  
  have h₃ : (Γ' ⊢₅ (f →' ⊥)),
  apply proof.ctx,
  apply cons_ext_max_sub,
  finish,

  have h₄ : (Γ' ⊢₅ ⊥) := proof.mp _ _ _ mdl h₃,
  have h₅ := cons_ext_max_cons _ h₁,
  contradiction,

  assumption,
  intros f' h₃,
  rw [←CanonS5_v_equiv],
  simp [v_mem],
  apply cons_ext_max_sub,
  finish,

  intro _,
  simp [consistent] at h₁,
  rw deduction_S5 at h₁,
  
  have h₂ := lift_S5 _ _ (dneg_elim_PC Γ f),
  have h₃ := proof.mp _ _ _ h₁ h₂,
  assumption,
end

theory ContextReconstruct
  imports Cogent
begin

section {* split and weakening rules for minimal contexts *}

text {*
  These are slightly different from the core rules
*}

(*
subsection {* Split Definition *}

inductive split_comp_min :: "kind env \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> bool"
          ("_ \<turnstile> _ m\<leadsto> _ \<parallel> _" [30,0,0,20] 60) where
  none_min  : "K \<turnstile> None m\<leadsto> None \<parallel> None"
| left_min  : "\<lbrakk> K \<turnstile> t :\<kappa> k         \<rbrakk> \<Longrightarrow> K \<turnstile> Some t m\<leadsto> Some t \<parallel> None"
| right_min : "\<lbrakk> K \<turnstile> t :\<kappa> k         \<rbrakk> \<Longrightarrow> K \<turnstile> Some t m\<leadsto> None   \<parallel> (Some t)"
| share_min : "\<lbrakk> K \<turnstile> t :\<kappa> k ; S \<in> k \<rbrakk> \<Longrightarrow> K \<turnstile> Some t m\<leadsto> Some t \<parallel> Some t"

definition split_min :: "kind env \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool" ("_ \<turnstile> _ m\<leadsto> _ | _" [30,0,0,20] 60) where
  "split_min K \<equiv> list_all3 (split_comp K)"

lemmas split_min_induct[consumes 1, case_names split_empty split_cons, induct set: list_all3]
 = list_all3_induct[where P="split_comp K" for K, simplified split_def[symmetric]]

lemmas split_min_empty = all3Nil[where P="split_comp K" for K, simplified split_def[symmetric]]
lemmas split_min_cons = all3Cons[where P="split_comp K" for K, simplified split_def[symmetric]]
*)

subsection {* Split-bang Definition *}

inductive split_bang_min_comp :: "kind env \<Rightarrow> bool \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> bool" ("_ , _ \<turnstile> _ m\<leadsto>b _ \<parallel> _") where
  none     : "K \<turnstile> x \<leadsto> a \<parallel> b \<Longrightarrow> K , False \<turnstile> x m\<leadsto>b a \<parallel> b"
| dobang   : "K \<turnstile> t :\<kappa> k \<Longrightarrow> K , True \<turnstile> Some t m\<leadsto>b Some (bang t) \<parallel> Some t"
| bangdrop : "\<lbrakk> K \<turnstile> t :\<kappa> k ; D \<in> k \<rbrakk> \<Longrightarrow> K , True \<turnstile> Some t m\<leadsto>b Some (bang t) \<parallel> None"

inductive split_bang_min :: "kind env \<Rightarrow> index set \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool"  ("_ , _ \<turnstile> _ m\<leadsto>b _ | _" [30,0,0,20] 60) where
  split_bang_min_empty : "K , is \<turnstile> [] m\<leadsto>b [] | []"
| split_bang_min_cons  : "\<lbrakk> is' = pred ` Set.remove (0 :: index) is
                          ; K , is'  \<turnstile> xs m\<leadsto>b as | bs
                          ; K, (0 \<in> is) \<turnstile> x m\<leadsto>b a \<parallel> b
                          \<rbrakk> \<Longrightarrow> K , is \<turnstile> x # xs m\<leadsto>b a # as | b # bs"

(*
subsection {* Weakening Definition *}

inductive weakening_comp_min :: "kind env \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> bool" where
  none : "weakening_comp_min K None None"
| keep : "\<lbrakk> K \<turnstile> t :\<kappa> k \<rbrakk>         \<Longrightarrow> weakening_comp_min K (Some t) (Some t)"
| drop : "\<lbrakk> K \<turnstile> t :\<kappa> k ; D \<in> k \<rbrakk> \<Longrightarrow> weakening_comp_min K (Some t) None"

definition weakening_min :: "kind env \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool" ("_ \<turnstile> _ m\<leadsto>w _" [30,0,20] 60) where
  "weakening_min K \<equiv> list_all2 (weakening_comp_min K)"
*)

section {* Lemmas about split and weakening *}

lemma split_bang_into_split_bang_min:
  "K , is \<turnstile> a \<leadsto>b a1 \<parallel> a2 \<Longrightarrow> K , is \<turnstile> a m\<leadsto>b a1 \<parallel> a2"
  by (force elim: split_bang_comp.cases intro: split_bang_min_comp.intros)

(* n.b. these will eventually be between core and min-ctx definitions *)

lemma split_weaken_comp:
  assumes "K \<turnstile> a \<leadsto> a1 \<parallel> a2"
    and "weakening_comp K a wa"
  shows "\<exists>wa1 wa2. (K \<turnstile> wa \<leadsto> wa1 \<parallel> wa2) \<and> (weakening_comp K a1 wa1) \<and> (weakening_comp K a2 wa2)"
  using assms
  apply (cases a1)
   apply (fastforce simp add: split_comp.simps weakening_comp.simps)
  apply (cases a2)
   apply (fastforce simp add: split_comp.simps weakening_comp.simps)
  apply (clarsimp simp add: split_comp.simps weakening_comp.simps, blast)
  done

lemma split_weaken:
  assumes "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    and "K \<turnstile> \<Gamma> \<leadsto>w w\<Gamma>"
  shows "\<exists>w\<Gamma>1 w\<Gamma>2. (K \<turnstile> w\<Gamma> \<leadsto> w\<Gamma>1 | w\<Gamma>2) \<and> (K \<turnstile> \<Gamma>1 \<leadsto>w w\<Gamma>1) \<and> (K \<turnstile> \<Gamma>2 \<leadsto>w w\<Gamma>2)"
  using assms
proof (induct \<Gamma> arbitrary: w\<Gamma> \<Gamma>1 \<Gamma>2)
  case Nil
  then show ?case
    using split_length weakening_length by fastforce
next
  case (Cons a \<Gamma>')
  then obtain a1 \<Gamma>1' a2 \<Gamma>2' wa w\<Gamma>'
    where ctx_simps:
      "\<Gamma>1 = a1 # \<Gamma>1'"
      "\<Gamma>2 = a2 # \<Gamma>2'"
      "w\<Gamma> = wa # w\<Gamma>'"
    using weakening_def split_length
    by (metis list.rel_distinct(2) length_0_conv neq_Nil_conv)

  have prems_elims:
    "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1' | \<Gamma>2'"
    "K \<turnstile> a \<leadsto> a1 \<parallel> a2"
    "K \<turnstile> \<Gamma>' \<leadsto>w w\<Gamma>'"
    "weakening_comp K a wa"
    using Cons.prems
    by (fastforce simp add: split_def elim: list_all3.cases simp add: weakening_def ctx_simps)+
  then obtain wa1 wa2
    where weak_of_split_comps:
      "K \<turnstile> wa \<leadsto> wa1 \<parallel> wa2"
      "weakening_comp K a1 wa1"
      "weakening_comp K a2 wa2"
    using split_weaken_comp by blast

  obtain w\<Gamma>1' w\<Gamma>2'
    where ih_on_subctxs:
      "K \<turnstile> w\<Gamma>' \<leadsto> w\<Gamma>1' | w\<Gamma>2'"
      "K \<turnstile> \<Gamma>1' \<leadsto>w w\<Gamma>1'"
      "K \<turnstile> \<Gamma>2' \<leadsto>w w\<Gamma>2'"
    using prems_elims Cons.hyps weakening_def split_cons prems_elims
    by blast

  have "K \<turnstile> wa # w\<Gamma>' \<leadsto> wa1 # w\<Gamma>1' | wa2 # w\<Gamma>2'"
    and "K \<turnstile> a1 # \<Gamma>1' \<leadsto>w wa1 # w\<Gamma>1'"
    and "K \<turnstile> a2 # \<Gamma>2' \<leadsto>w wa2 # w\<Gamma>2'"
    using ih_on_subctxs weak_of_split_comps split_cons weakening_def list.rel_intros(2)
    by metis+
  then show ?case
    using ctx_simps by blast
qed


lemma weaken_and_split_comp:
  assumes "K \<turnstile> a \<leadsto> a1 \<parallel> a2"
    and "weakening_comp K a1 wa1"
    and "weakening_comp K a2 wa2"
  shows "\<exists>wa. weakening_comp K a wa \<and> K \<turnstile> wa \<leadsto> wa1 \<parallel> wa2"
  using assms
  by (fastforce simp add: split_comp.simps weakening_comp.simps)

lemma weaken_and_split:
  assumes "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    and "K \<turnstile> \<Gamma>1 \<leadsto>w w\<Gamma>1"
    and "K \<turnstile> \<Gamma>2 \<leadsto>w w\<Gamma>2"
  shows "\<exists>w\<Gamma>. (K \<turnstile> \<Gamma> \<leadsto>w w\<Gamma>) \<and> (K \<turnstile> w\<Gamma> \<leadsto> w\<Gamma>1 | w\<Gamma>2)"
  using assms
proof (induct arbitrary: w\<Gamma>1 w\<Gamma>2 rule: split_induct)
  case (split_cons a \<Gamma> a1 \<Gamma>1 a2 \<Gamma>2)

  obtain wa1 w\<Gamma>1' wa2 w\<Gamma>2'
    where ctx_simps:
      "w\<Gamma>1 = wa1 # w\<Gamma>1'"
      "w\<Gamma>2 = wa2 # w\<Gamma>2'"
    by (metis split_cons.prems list_all2_Cons1 weakening_def)
  have subweakenings:
    "weakening_comp K a1 wa1"
    "K \<turnstile> \<Gamma>1 \<leadsto>w w\<Gamma>1'"
    "weakening_comp K a2 wa2"
    "K \<turnstile> \<Gamma>2 \<leadsto>w w\<Gamma>2'"
    by (metis ctx_simps list.rel_inject(2) split_cons.prems weakening_def)+
  then obtain w\<Gamma>' wa
    where IHsplitsweakens:
      "K \<turnstile> wa \<leadsto> wa1 \<parallel> wa2"
      "K \<turnstile> w\<Gamma>' \<leadsto> w\<Gamma>1'| w\<Gamma>2'"
      "weakening_comp K a wa"
      "K \<turnstile> \<Gamma> \<leadsto>w w\<Gamma>'"
    using split_cons.hyps weaken_and_split_comp
    by blast
  then have
    "K \<turnstile> wa # w\<Gamma>' \<leadsto> wa1 # w\<Gamma>1' | wa2 # w\<Gamma>2'"
    "K \<turnstile> a # \<Gamma> \<leadsto>w wa # w\<Gamma>'"
    unfolding weakening_def
    using IHsplitsweakens
    by (simp add: split_def weakening_def)+
  then show ?case
    using ctx_simps by blast
qed (force simp add: weakening_def split_def)

lemma weaken_and_split_bang_comp:
  assumes "K , dobang \<turnstile> a \<leadsto>b a1 \<parallel> a2"
    and "weakening_comp K a1 wa1"
    and "weakening_comp K a2 wa2"
  shows "\<exists>wa dobang. (weakening_comp K a wa) \<and> (K , dobang \<turnstile> wa m\<leadsto>b wa1 \<parallel> wa2)"
  using assms
proof (cases rule: split_bang_comp.cases)
  case none
  then show ?thesis
    using assms
    apply -
    apply (erule split_comp.cases)
       apply (fastforce simp add: split_comp.simps weakening_comp.simps split_bang_min_comp.simps)
      apply clarsimp
      apply (cases wa1)
       apply (auto simp add: weakening_comp.simps split_bang_min_comp.simps split_comp.simps)[1]
      apply (clarsimp simp add: weakening_comp.simps split_bang_min_comp.simps split_comp.simps, meson)
     apply (cases wa2)
      apply (auto simp add: weakening_comp.simps split_bang_min_comp.simps split_comp.simps)[2]
    apply (cases wa1; cases wa2)
       apply (auto simp add: weakening_comp.simps split_bang_min_comp.simps split_comp.simps)[4]
    done
next
  case (dobang x)
  then show ?thesis
    using assms
    by (cases wa1; cases wa2;
            (clarsimp simp add: weakening_comp.simps split_bang_min_comp.simps split_comp.simps, auto))
qed


lemma weaken_and_split_bang:
  assumes "K , is \<turnstile> \<Gamma> \<leadsto>b \<Gamma>1 | \<Gamma>2"
    and "K \<turnstile> \<Gamma>1 \<leadsto>w w\<Gamma>1"
    and "K \<turnstile> \<Gamma>2 \<leadsto>w w\<Gamma>2"
  shows "\<exists>w\<Gamma> is. (K \<turnstile> \<Gamma> \<leadsto>w w\<Gamma>) \<and> (K , is \<turnstile> w\<Gamma> m\<leadsto>b w\<Gamma>1 | w\<Gamma>2)"
  using assms
proof (induct arbitrary: w\<Gamma>1 w\<Gamma>2 "is" rule: split_bang.inducts)
  case (split_bang_cons is' "is" K \<Gamma>' \<Gamma>1' \<Gamma>2' a a1 a2)

  obtain w\<Gamma>1' w\<Gamma>2' wa1 wa2
    where ctx_simps:
      "w\<Gamma>1 = wa1 # w\<Gamma>1'"
      "w\<Gamma>2 = wa2 # w\<Gamma>2'"
    using split_bang_cons.prems
    by (fastforce simp add: list_all2_Cons1 weakening_def)
  then have subweakenings:
    "weakening_comp K a1 wa1"
    "weakening_comp K a2 wa2"
    "K \<turnstile> \<Gamma>1' \<leadsto>w w\<Gamma>1'"
    "K \<turnstile> \<Gamma>2' \<leadsto>w w\<Gamma>2'"
    using split_bang_cons.prems weakening_nth
    by (fastforce simp add: weakening_def)+

  obtain w\<Gamma>' isa
    where IHresults:
      "K \<turnstile> \<Gamma>' \<leadsto>w w\<Gamma>'"
      "K , isa \<turnstile> w\<Gamma>' m\<leadsto>b w\<Gamma>1' | w\<Gamma>2'"
    using split_bang_cons.hyps(3) subweakenings by blast

  obtain wa dobang
    where weaken_split_bang_step:
      "weakening_comp K a wa"
      "K , dobang \<turnstile> wa m\<leadsto>b wa1 \<parallel> wa2"
    using split_bang_cons.hyps subweakenings weaken_and_split_bang_comp
    by blast

  have
    "K \<turnstile> a # \<Gamma>' \<leadsto>w wa # w\<Gamma>'"
    using weaken_split_bang_step IHresults
    by (simp add: weakening_def)
  moreover have "K , (if dobang then insert 0 (Suc ` isa) else Suc ` isa) \<turnstile> wa # w\<Gamma>' m\<leadsto>b wa1 # w\<Gamma>1' | wa2 # w\<Gamma>2'"
    using IHresults weaken_split_bang_step
    by (fastforce intro: split_bang_min.intros simp add: remove_def zero_notin_Suc_image set_pred_left_inverse_suc)
  ultimately show ?case
    using ctx_simps by fast
qed (simp add: split_bang_min_empty weakening_def)



section {* Functions for merging split contexts *}

(* The inner layer of option is whether the type is present in the context.
   The outer layer is whether the merge succeeded *)
fun merge_ctx_comp :: "kind env \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type option option" where
  "merge_ctx_comp K (Some x) (Some y) = (if (x = y) \<and> (\<exists>k. K \<turnstile> x :\<kappa> k \<and> S \<in> k)
                                              then Some (Some x)
                                              else None)"
| "merge_ctx_comp K (Some x) (None) = Some (Some x)"
| "merge_ctx_comp K (None) (Some y) = Some (Some y)"
| "merge_ctx_comp K (None) (None) = Some (None)"

fun merge_ctx :: "kind env \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx option" where
  "merge_ctx _ [] [] = Some []"
| "merge_ctx K (optx # \<Gamma>1) (opty # \<Gamma>2) = (case (merge_ctx_comp K optx opty) of
                                            (Some a) \<Rightarrow> (case (merge_ctx K \<Gamma>1 \<Gamma>2) of
                                                             (Some rest) \<Rightarrow> Some (a # rest)
                                                           | None \<Rightarrow> None)
                                          | None \<Rightarrow> None)"
| "merge_ctx a (v # va) [] = None"
| "merge_ctx a [] (v # va) = None" 

lemma split_imp_merge_ctx:
  assumes "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  shows "Some \<Gamma> = merge_ctx K \<Gamma>1 \<Gamma>2"
  using assms
proof (induct \<Gamma> arbitrary: \<Gamma>1 \<Gamma>2)
  case Nil
  then show ?case
    using split_length by fastforce
next
  case (Cons a \<Gamma>')
  obtain a1 \<Gamma>1' a2 \<Gamma>2'
    where subsplittings:
      "\<Gamma>1 = a1 # \<Gamma>1'"
      "\<Gamma>2 = a2 # \<Gamma>2'"
      "K \<turnstile> a \<leadsto> a1 \<parallel> a2"
      "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1' | \<Gamma>2'"
    using Cons.prems
    by (clarsimp simp add: split_def list_all3_Cons1)
  then show ?case
    using Cons.hyps
    by (auto simp add: split_comp.simps option_cases_boolean)
qed

lemma merge_ctx_comp_imp_split_comp:
  assumes "\<And>t. a = Some t \<Longrightarrow> K \<turnstile> t wellformed"
  and "\<And>t. b = Some t \<Longrightarrow> K \<turnstile> t wellformed"
and "merge_ctx_comp K a b = Some c"
shows "K \<turnstile> c \<leadsto> a \<parallel> b"
  using assms
  apply (cases rule: merge_ctx_comp.cases[where x="(K, a, b)"])
     apply (clarsimp simp add: ifthenelse_eq_as_boolean split_comp.simps)+
  done

lemma merge_ctx_imp_split:
  assumes "\<And>a. Some a \<in> set \<Gamma>1 \<Longrightarrow> K \<turnstile> a wellformed"
    and "\<And>a. Some a \<in> set \<Gamma>2 \<Longrightarrow> K \<turnstile> a wellformed"
    and "merge_ctx K \<Gamma>1 \<Gamma>2 = Some \<Gamma>"
  shows "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  using assms
proof (induct arbitrary: \<Gamma> rule: merge_ctx.induct)
  case (2 K optx \<Gamma>1 opty \<Gamma>2)
  moreover then obtain g \<Gamma>' where "\<Gamma> = g # \<Gamma>'"
    by (simp add: option_cases_boolean, blast)
  ultimately show ?case
    using split_cons
    by (simp add: option_cases_boolean merge_ctx_comp_imp_split_comp)
qed (simp add: split_def)+


fun merge_ctx_bang_comp :: "kind env \<Rightarrow> bool \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type option option" where
  "merge_ctx_bang_comp K False optx     opty     = merge_ctx_comp K optx opty"
| "merge_ctx_bang_comp K True  (Some x) (Some y) = (if x = bang y \<and> (\<exists>k. K \<turnstile> y :\<kappa> k) then Some (Some y) else None)"
| "merge_ctx_bang_comp K True  (Some x) None     = (SOME t'. (\<exists>t. t' = Some (Some t) \<and> x = bang t \<and> (\<exists>k. (K \<turnstile> t :\<kappa> k) \<and> D \<in> k)) \<or> t' = None)" (* TODO bad! *)
| "merge_ctx_bang_comp _ _         _        _    = None"

fun merge_ctx_bang :: "kind env \<Rightarrow> nat set \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx option" where
  "merge_ctx_bang K is [] [] = Some []"
| "merge_ctx_bang K is (optx # \<Gamma>1) (opty # \<Gamma>2) = (let is' = pred ` Set.remove (0 :: index) is
                                                      in (case merge_ctx_bang_comp K (0 \<in> is) optx opty of
                                                        Some a \<Rightarrow> (case merge_ctx_bang K is' \<Gamma>1 \<Gamma>2 of
                                                                     Some rest \<Rightarrow> Some (a # rest)
                                                                   | None \<Rightarrow> None)
                                                      | None \<Rightarrow> None))"
| "merge_ctx_bang _ _ (v # va) [] = None"
| "merge_ctx_bang _ _ [] (v # va) = None" 


lemma split_bang_imp_merge_ctx_bang:
  assumes "K , is \<turnstile> \<Gamma> m\<leadsto>b \<Gamma>1 | \<Gamma>2"
  shows "Some \<Gamma> = merge_ctx_bang K is \<Gamma>1 \<Gamma>2"
  using assms
proof (induct rule: split_bang_min.inducts)
  case (split_bang_min_cons is' "is" K xs as bs x a b)
  then show ?case
    apply (cases "0 \<notin> is")
     apply (auto simp: split_comp.simps split_bang_min_comp.simps option_cases_boolean)[1]
    apply (clarsimp simp add: split_comp.simps split_bang_min_comp.simps option_cases_boolean)
    apply (cases b; clarsimp)
    apply (intro some_equality, fast)
    apply (erule disjE; clarsimp)
    sorry
qed simp+


section {* minimal typing *}

inductive typing_minimal :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> ctx \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> ctx \<Rightarrow> bool"
          ("_, _, _ \<turnstile> _ :m _ \<stileturn> _" [30,0,0,0,0,20] 60)
      and typing_minimal_all :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> ctx \<Rightarrow> 'f expr list \<Rightarrow> type list \<Rightarrow> ctx \<Rightarrow> bool"
          ("_, _, _ \<turnstile>* _ :m _ \<stileturn> _" [30,0,0,0,0,20] 60) where

  typing_min_var    : "\<lbrakk> i < length \<Gamma>
                       ; K \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i t (* correctness *)
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Var i :m t \<stileturn> singleton (length \<Gamma>) i t"

| typing_min_afun   : "\<lbrakk> \<Xi> f = (K', t, u)
                       ; list_all2 (kinding K) ts K'
                       ; K' \<turnstile> TFun t u wellformed
                       ; K \<turnstile> \<Gamma> \<leadsto>w empty (length \<Gamma>) (* correctness *)
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> AFun f ts :m instantiate ts (TFun t u) \<stileturn> empty (length \<Gamma>)"

| typing_min_fun    : "\<lbrakk> \<Xi>, K', [Some t] \<turnstile> f :m u \<stileturn> \<Gamma>'
                       ; K' \<turnstile> t wellformed
                       ; list_all2 (kinding K) ts K'
                       ; K \<turnstile> \<Gamma> \<leadsto>w empty (length \<Gamma>) (* correctness *)
                       ; K'\<turnstile> [Some t] \<leadsto>w \<Gamma>' (* correctness *)
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Fun f ts :m instantiate ts (TFun t u) \<stileturn> empty (length \<Gamma>)"

| typing_min_app    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                       ; \<Xi>, K, \<Gamma>1 \<turnstile> a :m TFun x y \<stileturn> \<Gamma>1'
                       ; \<Xi>, K, \<Gamma>2 \<turnstile> b :m x \<stileturn> \<Gamma>2'
                       ; merge_ctx K \<Gamma>1' \<Gamma>2' = Some \<Gamma>'
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> App a b :m y \<stileturn> \<Gamma>'"

| typing_min_con    : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile> x :m t \<stileturn> \<Gamma>'
                       ; (tag, t, False) \<in> set ts
                       ; K \<turnstile>* (map (fst \<circ> snd) ts) wellformed
                       ; distinct (map fst ts)
                       ; map fst ts = map fst ts'
                       ; map (fst \<circ> snd) ts = map (fst \<circ> snd) ts'
                       ; list_all2 (\<lambda>x y. snd (snd y) \<longrightarrow> snd (snd x)) ts ts'
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Con ts tag x :m TSum ts' \<stileturn> \<Gamma>'"

| typing_min_cast   : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile> e :m TPrim (Num \<tau>) \<stileturn> \<Gamma>'
                       ; upcast_valid \<tau> \<tau>'
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Cast \<tau>' e :m TPrim (Num \<tau>') \<stileturn> \<Gamma>'"

| typing_min_tuple  : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                       ; \<Xi>, K, \<Gamma>1 \<turnstile> x :m t \<stileturn> \<Gamma>1'
                       ; \<Xi>, K, \<Gamma>2 \<turnstile> y :m u \<stileturn> \<Gamma>2'
                       ; merge_ctx K \<Gamma>1' \<Gamma>2' = Some \<Gamma>'
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Tuple x y :m TProduct t u \<stileturn> \<Gamma>'"

| typing_min_split  : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                       ; \<Xi>, K, \<Gamma>1 \<turnstile> x :m TProduct t u \<stileturn> \<Gamma>1'
                       ; \<Xi>, K, (Some t)#(Some u)#\<Gamma>2 \<turnstile> y :m t' \<stileturn> T' # U' # \<Gamma>2'
                       ; merge_ctx K \<Gamma>1' \<Gamma>2' = Some \<Gamma>'
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Split x y :m t' \<stileturn> \<Gamma>'"

| typing_min_let    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                       ; \<Xi>, K, \<Gamma>1 \<turnstile> x :m t \<stileturn> \<Gamma>1'
                       ; \<Xi>, K, (Some t # \<Gamma>2) \<turnstile> y :m u \<stileturn> T' # \<Gamma>2'
                       ; merge_ctx K \<Gamma>1' \<Gamma>2' = Some \<Gamma>'
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Let x y :m u \<stileturn> \<Gamma>'"

| typing_min_letb   : "\<lbrakk> K , is \<turnstile> \<Gamma> \<leadsto>b \<Gamma>1 | \<Gamma>2
                       ; \<Xi>, K, \<Gamma>1 \<turnstile> x :m t \<stileturn> \<Gamma>1'
                       ; \<Xi>, K, (Some t # \<Gamma>2) \<turnstile> y :m u \<stileturn> T' # \<Gamma>2'
                       ; K \<turnstile> t :\<kappa> k
                       ; E \<in> k
                       ; isa \<subseteq> is
                       ; merge_ctx_bang K isa \<Gamma>1' \<Gamma>2' = Some \<Gamma>'
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> LetBang is x y :m u \<stileturn> \<Gamma>'"

| typing_min_case   : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                       ; \<Xi>, K, \<Gamma>1 \<turnstile> x :m TSum ts \<stileturn> \<Gamma>1'
                       ; (tag, (t,False)) \<in> set ts
                       ; \<Xi>, K, (Some t # \<Gamma>2) \<turnstile> a :m u \<stileturn> T' # \<Gamma>2'
                       ; \<Xi>, K, (Some (TSum (tagged_list_update tag (t, True) ts)) # \<Gamma>2) \<turnstile> b :m u \<stileturn> X' # \<Gamma>2'
                       ; merge_ctx K \<Gamma>1' \<Gamma>2' = Some \<Gamma>'
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Case x tag a b :m u \<stileturn> \<Gamma>'"

| typing_min_esac   : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile> x :m TSum ts \<stileturn> \<Gamma>'
                       ; [(_, (t,False))] = filter (HOL.Not \<circ> snd \<circ> snd) ts
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Esac x :m t \<stileturn> \<Gamma>'"

| typing_min_if     : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                       ; \<Xi>, K, \<Gamma>1 \<turnstile> x :m TPrim Bool \<stileturn> \<Gamma>1'
                       ; \<Xi>, K, \<Gamma>2 \<turnstile> a :m t \<stileturn> \<Gamma>2'
                       ; \<Xi>, K, \<Gamma>2 \<turnstile> b :m t \<stileturn> \<Gamma>2'
                       ; merge_ctx K \<Gamma>1' \<Gamma>2' = Some \<Gamma>'
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> If x a b :m t \<stileturn> \<Gamma>'"

| typing_min_prim   : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile>* args :m map TPrim ts \<stileturn> \<Gamma>'
                       ; prim_op_type oper = (ts,t)
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Prim oper args :m TPrim t \<stileturn> \<Gamma>'"

| typing_min_lit    : "\<lbrakk> K \<turnstile> \<Gamma> consumed
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Lit l :m TPrim (lit_type l) \<stileturn> empty (length \<Gamma>)"

| typing_min_unit   : "\<lbrakk> K \<turnstile> \<Gamma> consumed
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Unit :m TUnit \<stileturn> empty (length \<Gamma>)"

| typing_min_struct : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile>* es :m ts \<stileturn> \<Gamma>'
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Struct ts es :m TRecord (zip ts (replicate (length ts) False)) Unboxed \<stileturn> \<Gamma>'"

| typing_min_member : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile> e :m TRecord ts s \<stileturn> \<Gamma>'
                       ; K \<turnstile> TRecord ts s :\<kappa> k
                       ; S \<in> k
                       ; f < length ts
                       ; ts ! f = (t, False)
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Member e f :m t \<stileturn> \<Gamma>'"

| typing_min_take   : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                       ; \<Xi>, K, \<Gamma>1 \<turnstile> e :m TRecord ts s \<stileturn> \<Gamma>1'
                       ; sigil_perm s \<noteq> Some ReadOnly
                       ; f < length ts
                       ; ts ! f = (t, False)
                       ; K \<turnstile> t :\<kappa> k
                       ; S \<in> k \<or> taken
                       ; \<Xi>, K, (Some t # Some (TRecord (ts [f := (t,taken)]) s) # \<Gamma>2) \<turnstile> e' :m u \<stileturn> T' # X' # \<Gamma>2'
                       ; merge_ctx K \<Gamma>1' \<Gamma>2' = Some \<Gamma>'
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Take e f e' :m u \<stileturn> \<Gamma>'"

| typing_min_put    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                       ; \<Xi>, K, \<Gamma>1 \<turnstile> e :m TRecord ts s \<stileturn> \<Gamma>1'
                       ; sigil_perm s \<noteq> Some ReadOnly
                       ; f < length ts
                       ; ts ! f = (t, taken)
                       ; K \<turnstile> t :\<kappa> k
                       ; D \<in> k \<or> taken
                       ; \<Xi>, K, \<Gamma>2 \<turnstile> e' :m t \<stileturn> \<Gamma>2'
                       ; merge_ctx K \<Gamma>1' \<Gamma>2' = Some \<Gamma>'
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Put e f e' :m TRecord (ts [f := (t,False)]) s \<stileturn> \<Gamma>'"

| typing_min_all_empty : "\<Xi>, K, empty n \<turnstile>* [] :m [] \<stileturn> empty n"

| typing_min_all_cons  : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                          ; \<Xi>, K, \<Gamma>1 \<turnstile>  e  :m t \<stileturn> \<Gamma>1'
                          ; \<Xi>, K, \<Gamma>2 \<turnstile>* es :m ts \<stileturn>  \<Gamma>2'
                          ; merge_ctx K \<Gamma>1' \<Gamma>2' = Some \<Gamma>'
                          \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>* (e # es) :m (t # ts) \<stileturn> \<Gamma>'"


lemma typing_min_to_kinding:
  shows "\<Xi>, K, \<Gamma> \<turnstile>  e  :m t  \<stileturn> \<Gamma>' \<Longrightarrow> K \<turnstile>  t  wellformed"
    and "\<Xi>, K, \<Gamma> \<turnstile>* es :m ts \<stileturn> \<Gamma>' \<Longrightarrow> K \<turnstile>* ts wellformed"
proof (induct rule: typing_minimal_typing_minimal_all.inducts)
  case typing_min_var then show ?case
    by (fastforce
        dest: weakening_preservation_some weakening_nth
        elim: weakening_comp.cases)
next case typing_min_fun    then show ?case
    by (fastforce intro: kinding_kinding_all_kinding_record.intros substitutivity)
next case typing_min_afun   then show ?case
    by (fastforce intro: kinding_kinding_all_kinding_record.intros substitutivity)
next case typing_min_con    then show ?case
    by (fastforce
        simp add: kinding_all_set
        intro!: kinding_kinding_all_kinding_record.intros)
next case typing_min_esac   then show ?case
    by (fastforce
        dest: filtered_member
        elim: kinding.cases
        simp add: kinding_all_set)
next case typing_min_member then show ?case
    by (fastforce intro: kinding_record_wellformed_nth)
next case typing_min_struct then show ?case 
    by (clarsimp , intro exI kind_trec kinding_all_record , simp_all add: kind_top)
next case typing_min_put    then show ?case
    by (fastforce intro: kinding_kinding_all_kinding_record.intros  kinding_record_update)
qed (auto intro: supersumption kinding_kinding_all_kinding_record.intros)


lemma minimal_typing_imp_weakening:
  shows "\<Xi>, K, \<Gamma> \<turnstile> e :m t \<stileturn> \<Gamma>' \<Longrightarrow> K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
    and "\<Xi>, K, \<Gamma> \<turnstile>* es :m ts \<stileturn> \<Gamma>' \<Longrightarrow> K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
proof (induct rule: typing_minimal_typing_minimal_all.inducts)
  case (typing_min_letb K "is" \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t \<Gamma>1' y u T' \<Gamma>2' k isa \<Gamma>')

  have weaken_\<Gamma>2:
    "K \<turnstile> \<Gamma>2 \<leadsto>w \<Gamma>2'"
    using typing_min_letb
    by (simp add: weakening_def)
  then obtain \<Gamma>'' isb \<Gamma>1'3
    where weaken_and_split\<Gamma>:
      "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>''"
      "K , isb \<turnstile> \<Gamma>'' m\<leadsto>b \<Gamma>1' | \<Gamma>2'"
    using weaken_and_split_bang typing_min_letb
    by meson
  moreover then have "merge_ctx_bang K isb \<Gamma>1' \<Gamma>2' = Some \<Gamma>''"
    by (simp add: split_bang_imp_merge_ctx_bang)
  moreover then have "\<Gamma>'' = \<Gamma>'"
    using typing_min_letb.hyps(8-9)
    sorry
  ultimately show ?case
    using weaken_and_split\<Gamma> typing_min_letb
    by simp
next
  case (typing_min_all_empty \<Xi> K n)
  then show ?case
    by (simp add: empty_def weakening_def list_all2_same weakening_comp.none)
qed (fastforce dest: weaken_and_split split_imp_merge_ctx simp add: weakening_cons)+

(* unnecessary once the proper soundness lemma is proven *)
lemma minimal_typing_preserves_ctx_length:
  shows "\<Xi>, K, \<Gamma> \<turnstile> e :m t \<stileturn> \<Gamma>' \<Longrightarrow> length \<Gamma> = length \<Gamma>'"
    and "\<Xi>, K, \<Gamma> \<turnstile>* es :m ts \<stileturn> \<Gamma>' \<Longrightarrow> length \<Gamma> = length \<Gamma>'"
proof (induct rule: typing_minimal_typing_minimal_all.inducts)
  case (typing_min_app K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> a x y \<Gamma>1' b \<Gamma>2')
  then show ?case
    using minimal_typing_imp_weakening
    by (blast intro: typing_minimal_typing_minimal_all.intros dest: weakening_length)
next
  case (typing_min_tuple K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t \<Gamma>1' y u \<Gamma>2')
  then show ?case
    using minimal_typing_imp_weakening
    by (blast intro: typing_minimal_typing_minimal_all.intros dest: weakening_length)
next
  case (typing_min_split K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t u \<Gamma>1' y t' T' U' \<Gamma>2')
  then show ?case
    using minimal_typing_imp_weakening
    by (blast intro: typing_minimal_typing_minimal_all.intros dest: weakening_length)
next
  case (typing_min_let K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t \<Gamma>1' y u T' \<Gamma>2')
  then show ?case
    using minimal_typing_imp_weakening
    by (blast intro: typing_minimal_typing_minimal_all.intros dest: weakening_length)
next
  case (typing_min_letb K "is" \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t \<Gamma>1' y u T' \<Gamma>2' k)
  then show ?case
    using minimal_typing_imp_weakening
    by (blast intro: typing_minimal_typing_minimal_all.intros dest: weakening_length)
next
  case (typing_min_case K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x ts \<Gamma>1' tag t a u T' \<Gamma>2' b X')
  then show ?case
    using minimal_typing_imp_weakening
    by (blast intro: typing_minimal_typing_minimal_all.intros dest: weakening_length)
next
  case (typing_min_esac \<Xi> K \<Gamma> x ts \<Gamma>' uu t)
  then show ?case
    using minimal_typing_imp_weakening
    by (blast intro: typing_minimal_typing_minimal_all.intros dest: weakening_length)
next
  case (typing_min_if K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x \<Gamma>1' a t \<Gamma>2' b)
  then show ?case
    using minimal_typing_imp_weakening
    by (blast intro: typing_minimal_typing_minimal_all.intros dest: weakening_length)
next
  case (typing_min_take K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s \<Gamma>1' f t k taken e' u T' X' \<Gamma>2')
  then show ?case
    using minimal_typing_imp_weakening
    by (blast intro: typing_minimal_typing_minimal_all.intros dest: weakening_length)
next
  case (typing_min_put K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s \<Gamma>1' f t taken k e' \<Gamma>2')
  then show ?case
    using minimal_typing_imp_weakening
    by (blast intro: typing_minimal_typing_minimal_all.intros dest: weakening_length)
next
  case (typing_min_all_cons K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e t \<Gamma>1' es ts \<Gamma>2')
  then show ?case
    using minimal_typing_imp_weakening
    by (blast intro: typing_minimal_typing_minimal_all.intros dest: weakening_length)
qed (auto intro: typing_minimal_typing_minimal_all.intros dest: split_imp_merge_ctx weakening_length)+


lemma minimal_typing_soundness:
(*
when we remove the \<Gamma>, we will need the full lemma, for now, we get it for free
  shows "\<Xi>, K, \<Gamma> \<turnstile> e : t \<Longrightarrow> \<exists>\<Gamma>'. (\<Xi>, K, \<Gamma> \<turnstile> e :m t \<stileturn> \<Gamma>') \<and> (K \<turnstile> \<Gamma> \<leadsto>w  \<Gamma>')"
    and "\<Xi>, K, \<Gamma> \<turnstile>* es : ts \<Longrightarrow> \<exists>\<Gamma>'. (\<Xi>, K, \<Gamma> \<turnstile>* es :m ts \<stileturn> \<Gamma>') \<and> (K \<turnstile> \<Gamma> \<leadsto>w  \<Gamma>')"
*)
  shows "\<Xi>, K, \<Gamma> \<turnstile> e : t \<Longrightarrow> \<exists>\<Gamma>'. (\<Xi>, K, \<Gamma> \<turnstile> e :m t \<stileturn> \<Gamma>')"
    and "\<Xi>, K, \<Gamma> \<turnstile>* es : ts \<Longrightarrow> \<exists>\<Gamma>'. (\<Xi>, K, \<Gamma> \<turnstile>* es :m ts \<stileturn> \<Gamma>')"
proof (induct rule: typing_typing_all.inducts)
  case (typing_afun \<Xi> f K' t u K ts \<Gamma>)
  then show ?case
    using is_consumed_def by (blast intro: typing_minimal_typing_minimal_all.intros)
next
  case (typing_fun \<Xi> K' t f u K \<Gamma> ts)
  then show ?case
    using is_consumed_def
    by (auto
        simp del: instantiate.simps
        intro: minimal_typing_imp_weakening
        intro!: typing_minimal_typing_minimal_all.intros exI[where x="Cogent.empty (length \<Gamma>)"])
next
  case (typing_app K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> a x y b)
  moreover then obtain \<Gamma>1' \<Gamma>2'
    where
      "\<Xi>, K, \<Gamma>1 \<turnstile> a :m TFun x y \<stileturn> \<Gamma>1'"
      "\<Xi>, K, \<Gamma>2 \<turnstile> b :m x \<stileturn> \<Gamma>2'"
      "K \<turnstile> \<Gamma>1 \<leadsto>w \<Gamma>1'"
      "K \<turnstile> \<Gamma>2 \<leadsto>w \<Gamma>2'"
    using minimal_typing_imp_weakening(1) by blast
  moreover then obtain \<Gamma>' where "merge_ctx K \<Gamma>1' \<Gamma>2' = Some \<Gamma>'"
    using typing_app weaken_and_split split_imp_merge_ctx by metis
  ultimately show ?case
    by (auto intro: typing_minimal_typing_minimal_all.intros)
next
  case (typing_tuple K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> t T u U)
  moreover then obtain \<Gamma>1' \<Gamma>2'
    where
      "\<Xi>, K, \<Gamma>1 \<turnstile> t :m T \<stileturn> \<Gamma>1'"
      "\<Xi>, K, \<Gamma>2 \<turnstile> u :m U \<stileturn> \<Gamma>2'"
      "K \<turnstile> \<Gamma>1 \<leadsto>w \<Gamma>1'"
      "K \<turnstile> \<Gamma>2 \<leadsto>w \<Gamma>2'"
    using minimal_typing_imp_weakening(1) by blast
  moreover then obtain \<Gamma>' where "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>' \<and> K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1' | \<Gamma>2'"
    using typing_tuple weaken_and_split by blast
  moreover then have "merge_ctx K \<Gamma>1' \<Gamma>2' = Some \<Gamma>'"
    using split_imp_merge_ctx by fastforce
  ultimately show ?case
    by (auto intro: typing_minimal_typing_minimal_all.intros)
next
  case (typing_split K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t u y t')
  moreover then obtain \<Gamma>1' TU\<Gamma>2'
    where IHresults:
      "\<Xi>, K, \<Gamma>1 \<turnstile> x :m TProduct t u \<stileturn> \<Gamma>1'"
      "\<Xi>, K, Some t # Some u # \<Gamma>2 \<turnstile> y :m t' \<stileturn> TU\<Gamma>2'"
      "K \<turnstile> \<Gamma>1 \<leadsto>w \<Gamma>1'"
      "K \<turnstile> Some t # Some u # \<Gamma>2 \<leadsto>w TU\<Gamma>2'"
    using minimal_typing_imp_weakening(1) by blast
  moreover then obtain T U \<Gamma>2'
    where ctx2_simps:
      "TU\<Gamma>2' = T # U # \<Gamma>2'"
      "weakening_comp K (Some t) T"
      "weakening_comp K (Some u) U"
      "K \<turnstile> \<Gamma>2 \<leadsto>w \<Gamma>2'"
    by (metis list_all2_Cons1 weakening_def)
  moreover obtain \<Gamma>' where "merge_ctx K \<Gamma>1' \<Gamma>2' = Some \<Gamma>'"
    using typing_split IHresults ctx2_simps weaken_and_split split_imp_merge_ctx
    by metis
  ultimately show ?case
    by (auto intro: typing_minimal_typing_minimal_all.intros)
next
  case (typing_let K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t y u)
  moreover then obtain \<Gamma>1' T\<Gamma>2'
    where IHresults:
      "\<Xi>, K, \<Gamma>1 \<turnstile> x :m t \<stileturn> \<Gamma>1'"
      "\<Xi>, K, Some t # \<Gamma>2 \<turnstile> y :m u \<stileturn> T\<Gamma>2'"
      "K \<turnstile> \<Gamma>1 \<leadsto>w \<Gamma>1'"
      "K \<turnstile> Some t # \<Gamma>2 \<leadsto>w T\<Gamma>2'"
    using minimal_typing_imp_weakening(1) by blast
  moreover then obtain T \<Gamma>2'
    where ctx2_simps:
      "T\<Gamma>2' = T # \<Gamma>2'"
      "weakening_comp K (Some t) T"
      "K \<turnstile> \<Gamma>2 \<leadsto>w \<Gamma>2'"
    by (metis list_all2_Cons1 weakening_def)
  moreover obtain \<Gamma>' where "merge_ctx K \<Gamma>1' \<Gamma>2' = Some \<Gamma>'"
    using typing_let IHresults ctx2_simps weaken_and_split split_imp_merge_ctx
    by metis
  ultimately show ?case
    by (auto intro: typing_minimal_typing_minimal_all.intros)
next
  case (typing_letb K "is" \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t y u k)
  moreover then obtain \<Gamma>1' T\<Gamma>2'
    where IHresults:
      "\<Xi>, K, \<Gamma>1 \<turnstile> x :m t \<stileturn> \<Gamma>1'"
      "\<Xi>, K, Some t # \<Gamma>2 \<turnstile> y :m u \<stileturn> T\<Gamma>2'"
      "K \<turnstile> \<Gamma>1 \<leadsto>w \<Gamma>1'"
      "K \<turnstile> Some t # \<Gamma>2 \<leadsto>w T\<Gamma>2'"
    using minimal_typing_imp_weakening(1) by blast
  moreover then obtain T \<Gamma>2'
    where ctx2_simps:
      "T\<Gamma>2' = T # \<Gamma>2'"
      "weakening_comp K (Some t) T"
      "K \<turnstile> \<Gamma>2 \<leadsto>w \<Gamma>2'"
    by (metis list_all2_Cons1 weakening_def)
  ultimately show ?case
    apply clarsimp
    apply (rename_tac G1 G2)
    apply (rule exI)
    apply (rule)
          apply simp
         apply simp
        apply simp
       apply simp
      apply simp
     apply (clarsimp simp add: weakening_cons)
    sorry
next
  case (typing_case K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x ts tag t a u b)
  moreover then obtain \<Gamma>1' T\<Gamma>2a' U\<Gamma>2b'
    where IHresults:
      "\<Xi>, K, \<Gamma>1 \<turnstile> x :m TSum ts \<stileturn> \<Gamma>1'"
      "\<Xi>, K, Some t # \<Gamma>2 \<turnstile> a :m u \<stileturn> T\<Gamma>2a'"
      "\<Xi>, K, Some (TSum (tagged_list_update tag (t, True) ts)) # \<Gamma>2 \<turnstile> b :m u \<stileturn> U\<Gamma>2b'"
      "K \<turnstile> \<Gamma>1 \<leadsto>w \<Gamma>1'"
      "K \<turnstile> Some t # \<Gamma>2 \<leadsto>w T\<Gamma>2a'"
      "K \<turnstile> Some (TSum (tagged_list_update tag (t, True) ts)) # \<Gamma>2 \<leadsto>w U\<Gamma>2b'"
    using minimal_typing_imp_weakening(1) by blast
  moreover then obtain T \<Gamma>2a' U \<Gamma>2b'
    where ctx2_simps:
      "T\<Gamma>2a' = T # \<Gamma>2a'"
      "weakening_comp K (Some t) T"
      "K \<turnstile> \<Gamma>2 \<leadsto>w \<Gamma>2a'"
      "U\<Gamma>2b' = U # \<Gamma>2b'"
      "weakening_comp K (Some (TSum (tagged_list_update tag (t, True) ts))) U"
      "K \<turnstile> \<Gamma>2 \<leadsto>w \<Gamma>2b'"
    by (fastforce simp add: list_all2_Cons1 weakening_def)
  moreover have "\<Gamma>2a' = \<Gamma>2b'"
    sorry
  moreover obtain \<Gamma>' where "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>' \<and> K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1' | \<Gamma>2a'"
    using typing_case IHresults ctx2_simps weaken_and_split
    by blast
  moreover then have "merge_ctx K \<Gamma>1' \<Gamma>2a' = Some \<Gamma>'"
    using split_imp_merge_ctx by fastforce
  ultimately show ?case
    by (auto intro: typing_minimal_typing_minimal_all.intros)
next
  case (typing_if K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x a t b)
  then show ?case
    apply clarsimp
    apply (rename_tac \<Gamma>1' \<Gamma>2a \<Gamma>2b)
    apply (subgoal_tac "\<Gamma>2a = \<Gamma>2b")
(*
     apply (blast intro: typing_minimal_typing_minimal_all.intros)
*)
    sorry
next
  case (typing_take K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f t k taken e' u)
  moreover then obtain \<Gamma>1' TR\<Gamma>2'
    where IHresults:
      "\<Xi>, K, \<Gamma>1 \<turnstile> e :m TRecord ts s \<stileturn> \<Gamma>1'"
      "\<Xi>, K, Some t # Some (TRecord (ts[f := (t, taken)]) s) # \<Gamma>2 \<turnstile> e' :m u \<stileturn> TR\<Gamma>2'"
      "K \<turnstile> \<Gamma>1 \<leadsto>w \<Gamma>1'"
      "K \<turnstile> Some t # Some (TRecord (ts[f := (t, taken)]) s) # \<Gamma>2 \<leadsto>w TR\<Gamma>2'"
    using minimal_typing_imp_weakening(1) by blast
  moreover then obtain T R \<Gamma>2'
    where ctx2_simps:
      "TR\<Gamma>2' = T # R # \<Gamma>2'"
      "weakening_comp K (Some t) T"
      "weakening_comp K (Some (TRecord (ts[f := (t, taken)]) s)) R"
      "K \<turnstile> \<Gamma>2 \<leadsto>w \<Gamma>2'"
    by (fastforce simp add: list_all2_Cons1 weakening_def)
  moreover then obtain \<Gamma>' where "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>' \<and> K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1' | \<Gamma>2'"
    using typing_take IHresults weaken_and_split by blast
  moreover then have "merge_ctx K \<Gamma>1' \<Gamma>2' = Some \<Gamma>'"
    using split_imp_merge_ctx by fastforce
  ultimately show ?case
    by (auto intro: typing_minimal_typing_minimal_all.intros)
next
  case (typing_put K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f t taken k e')
  moreover then obtain \<Gamma>1' \<Gamma>2'
    where
      "\<Xi>, K, \<Gamma>1 \<turnstile> e :m TRecord ts s \<stileturn> \<Gamma>1'"
      "\<Xi>, K, \<Gamma>2 \<turnstile> e' :m t \<stileturn> \<Gamma>2'"
      "K \<turnstile> \<Gamma>1 \<leadsto>w \<Gamma>1'"
      "K \<turnstile> \<Gamma>2 \<leadsto>w \<Gamma>2'"
    using minimal_typing_imp_weakening(1) by blast
  moreover then obtain \<Gamma>' where "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>' \<and> K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1' | \<Gamma>2'"
    using typing_put weaken_and_split by blast
  moreover then have "merge_ctx K \<Gamma>1' \<Gamma>2' = Some \<Gamma>'"
    using split_imp_merge_ctx by fastforce
  ultimately show ?case
    by (auto intro: typing_minimal_typing_minimal_all.intros)
next
  case (typing_all_cons K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e t es ts)
    moreover then obtain \<Gamma>1' \<Gamma>2'
    where
      "\<Xi>, K, \<Gamma>1 \<turnstile> e :m t \<stileturn> \<Gamma>1'"
      "\<Xi>, K, \<Gamma>2 \<turnstile>* es :m ts \<stileturn> \<Gamma>2'"
      "K \<turnstile> \<Gamma>1 \<leadsto>w \<Gamma>1'"
      "K \<turnstile> \<Gamma>2 \<leadsto>w \<Gamma>2'"
    using minimal_typing_imp_weakening by fast
  moreover then obtain \<Gamma>' where "merge_ctx K \<Gamma>1' \<Gamma>2' = Some \<Gamma>'"
    using typing_all_cons weaken_and_split split_imp_merge_ctx by metis
  ultimately show ?case
    by (auto intro: typing_minimal_typing_minimal_all.intros)

qed (blast intro: typing_minimal_typing_minimal_all.intros)+


lemma minimal_typing_completeness:
  shows "\<Xi>, K, \<Gamma> \<turnstile> e :m t \<stileturn> \<Gamma>' \<Longrightarrow> \<Xi>, K, \<Gamma>' \<turnstile> e : t"
  and "\<Xi>, K, \<Gamma> \<turnstile>* es :m ts \<stileturn> \<Gamma>' \<Longrightarrow> \<Xi>, K, \<Gamma>' \<turnstile>* es : ts"
proof (induct rule: typing_minimal_typing_minimal_all.inducts)
  case (typing_min_fun \<Xi> K' t f u \<Gamma>' K ts \<Gamma>)
  moreover have "\<Gamma>' = [Some t] \<or> \<Gamma>' = [None]"
    by (metis length_0_conv list_all2_Cons1 typing_min_fun.hyps(6) weakening_comp.cases weakening_def weakening_length)
  ultimately show ?case
    apply (auto simp del: instantiate.simps intro: weakening_implies_wellformed weakening_refl intro!: typing_typing_all.intros)
      defer
      apply (auto simp del: instantiate.simps intro: weakening_implies_wellformed weakening_refl intro!: typing_typing_all.intros)
    sorry
next
  case (typing_min_app K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> a x y \<Gamma>1' b \<Gamma>2' \<Gamma>')
  then show ?case
    apply (auto simp del: instantiate.simps intro: weakening_implies_wellformed weakening_refl intro!: typing_typing_all.intros)
    using merge_ctx_imp_split minimal_typing_imp_weakening(1) weakening_implies_wellformed(2)
    by blast
next
  case (typing_min_tuple K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t \<Gamma>1' y u \<Gamma>2' \<Gamma>')
  then show ?case sorry
next
  case (typing_min_split K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t u \<Gamma>1' y t' T' U' \<Gamma>2' \<Gamma>')
  then show ?case sorry
next
  case (typing_min_let K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t \<Gamma>1' y u T' \<Gamma>2' \<Gamma>')
  then show ?case sorry
next
  case (typing_min_letb K "is" \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t \<Gamma>1' y u T' \<Gamma>2' k \<Gamma>')
  then show ?case sorry
next
  case (typing_min_case K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x ts \<Gamma>1' tag t a u T' \<Gamma>2' b X' \<Gamma>')
  then show ?case sorry
next
  case (typing_min_if K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x \<Gamma>1' a t \<Gamma>2' b \<Gamma>')
  then show ?case sorry
next
  case (typing_min_take K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s \<Gamma>1' f t k taken e' u T' X' \<Gamma>2' \<Gamma>')
  then show ?case sorry
next
  case (typing_min_put K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s \<Gamma>1' f t taken k e' \<Gamma>2' \<Gamma>')
  then show ?case sorry
next
  case (typing_min_all_cons K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e t \<Gamma>1' es ts \<Gamma>2' \<Gamma>')
  then show ?case sorry
qed (fastforce intro: weakening_implies_wellformed weakening_refl intro!: typing_typing_all.intros)+


lemma minimal_typing_generates_minimal_weakened:
  assumes "\<Xi>, K, \<Gamma> \<turnstile> e :m t \<stileturn> \<Gamma>'"
  shows "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
  and "\<And>\<Gamma>''. \<Xi>, K, \<Gamma>'' \<turnstile> e : t \<Longrightarrow> \<not> (K \<turnstile> \<Gamma>' \<leadsto>w \<Gamma>'')"
  sorry

end
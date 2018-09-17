theory ContextReconstruct
  imports Cogent
begin

fun merge_ctx :: "kind env \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx" where
  "merge_ctx K [] [] = []"
| "merge_ctx K (Some x # \<Gamma>1) (Some y # \<Gamma>2) = (if (x = y) \<and> (\<exists>k. K \<turnstile> x :\<kappa> k \<and> S \<in> k)
                                              then Some x # merge_ctx K \<Gamma>1 \<Gamma>2
                                              else undefined)"
| "merge_ctx K (Some x # \<Gamma>1) (None # \<Gamma>2) = Some x # merge_ctx K \<Gamma>1 \<Gamma>2"
| "merge_ctx K (None # \<Gamma>1) (Some y # \<Gamma>2) = Some y # merge_ctx K \<Gamma>1 \<Gamma>2"
| "merge_ctx K (None # \<Gamma>1) (None # \<Gamma>2) = None # merge_ctx K \<Gamma>1 \<Gamma>2"

lemma merge_ctx_correct:
  assumes "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  shows "\<Gamma> = merge_ctx K \<Gamma>1 \<Gamma>2"
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
    by (cases rule: split.cases, simp)
  then show ?case
    using Cons.hyps split_comp.simps by auto
qed

fun merge_ctx_bang :: "nat set \<Rightarrow> kind env \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx" where
  "merge_ctx_bang _ _ _ = undefined"


inductive typing_minimal :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> ctx \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> ctx \<Rightarrow> bool"
          ("_, _, _ \<turnstile> _ :m _ \<stileturn> _" [30,0,0,0,0,20] 60)
      and typing_minimal_all :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> ctx \<Rightarrow> 'f expr list \<Rightarrow> type list \<Rightarrow> ctx \<Rightarrow> bool"
          ("_, _, _ \<turnstile>* _ :m _ \<stileturn> _" [30,0,0,0,0,20] 60) where

  typing_min_var    : "\<lbrakk> i < length \<Gamma>
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Var i :m t \<stileturn> singleton (length \<Gamma>) i t"

| typing_min_afun   : "\<lbrakk> \<Xi> f = (K', t, u)
                   ; list_all2 (kinding K) ts K'
                   ; K' \<turnstile> TFun t u wellformed
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> AFun f ts :m instantiate ts (TFun t u) \<stileturn> empty (length \<Gamma>)"

| typing_min_fun    : "\<lbrakk> \<Xi>, K', [Some t] \<turnstile> f :m u \<stileturn> \<Gamma>1'
                   ; K' \<turnstile> t wellformed
                   ; list_all2 (kinding K) ts K'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Fun f ts :m instantiate ts (TFun t u) \<stileturn> empty (length \<Gamma>)"

| typing_min_app    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> a :m TFun x y \<stileturn> \<Gamma>1'
                   ; \<Xi>, K, \<Gamma>2 \<turnstile> b :m x \<stileturn> \<Gamma>2'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> App a b :m y \<stileturn> merge_ctx K \<Gamma>1 \<Gamma>2"

| typing_min_con    : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile> x :m t \<stileturn> \<Gamma>'
                   ; (tag, t, False) \<in> set ts
                   ; K \<turnstile>* (map (fst \<circ> snd) ts) wellformed
                   ; distinct (map fst ts)
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Con ts tag x :m TSum ts \<stileturn> \<Gamma>'"

| typing_min_cast   : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile> e :m TPrim (Num \<tau>) \<stileturn> \<Gamma>'
                   ; upcast_valid \<tau> \<tau>'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Cast \<tau>' e :m TPrim (Num \<tau>') \<stileturn> \<Gamma>'"

| typing_min_tuple  : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> x :m t \<stileturn> \<Gamma>1'
                   ; \<Xi>, K, \<Gamma>2 \<turnstile> y :m u \<stileturn> \<Gamma>2'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Tuple x y :m TProduct t u \<stileturn> merge_ctx K \<Gamma>1' \<Gamma>2'"

| typing_min_split  : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> x :m TProduct t u \<stileturn> \<Gamma>1'
                   ; \<Xi>, K, (Some t)#(Some u)#\<Gamma>2 \<turnstile> y :m t' \<stileturn> T' # U' # \<Gamma>2'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Split x y :m t' \<stileturn> merge_ctx K \<Gamma>1' \<Gamma>2'"

| typing_min_let    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> x :m t \<stileturn> \<Gamma>1'
                   ; \<Xi>, K, (Some t # \<Gamma>2) \<turnstile> y :m u \<stileturn> T' # \<Gamma>2'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Let x y :m u \<stileturn> merge_ctx K \<Gamma>1' \<Gamma>2'"

| typing_min_letb   : "\<lbrakk> split_bang K is \<Gamma> \<Gamma>1 \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> x :m t \<stileturn> \<Gamma>1'
                   ; \<Xi>, K, (Some t # \<Gamma>2) \<turnstile> y :m u \<stileturn> T' # \<Gamma>2'
                   ; K \<turnstile> t :\<kappa> k
                   ; E \<in> k
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> LetBang is x y :m u \<stileturn> merge_ctx_bang is K \<Gamma>1' \<Gamma>2'"

| typing_min_case   : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> x :m TSum ts \<stileturn> \<Gamma>1'
                   ; (tag, (t,False)) \<in> set ts
                   ; \<Xi>, K, (Some t # \<Gamma>2) \<turnstile> a :m u \<stileturn> T' # \<Gamma>2'
                   ; \<Xi>, K, (Some (TSum (tagged_list_update tag (t, True) ts)) # \<Gamma>2) \<turnstile> b :m u \<stileturn> X' # \<Gamma>2'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Case x tag a b :m u \<stileturn> merge_ctx K \<Gamma>1' \<Gamma>2'"

| typing_min_esac   : "\<lbrakk> \<Xi>, K, \<Gamma> \<turnstile> x :m TSum ts \<stileturn> \<Gamma>'
                   ; [(_, (t,False))] = filter (HOL.Not \<circ> snd \<circ> snd) ts
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Esac x :m t \<stileturn> \<Gamma>'"

| typing_min_if     : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> x :m TPrim Bool \<stileturn> \<Gamma>1'
                   ; \<Xi>, K, \<Gamma>2 \<turnstile> a :m t \<stileturn> \<Gamma>2'
                   ; \<Xi>, K, \<Gamma>2 \<turnstile> b :m t \<stileturn> \<Gamma>2'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> If x a b :m t \<stileturn> merge_ctx K \<Gamma>1' \<Gamma>2'"

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
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Take e f e' :m u \<stileturn> merge_ctx K \<Gamma>1' \<Gamma>2'"

| typing_min_put    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, K, \<Gamma>1 \<turnstile> e :m TRecord ts s \<stileturn> \<Gamma>1'
                   ; sigil_perm s \<noteq> Some ReadOnly
                   ; f < length ts
                   ; ts ! f = (t, taken)
                   ; K \<turnstile> t :\<kappa> k
                   ; D \<in> k \<or> taken
                   ; \<Xi>, K, \<Gamma>2 \<turnstile> e' :m t \<stileturn> \<Gamma>2'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Put e f e' :m TRecord (ts [f := (t,False)]) s \<stileturn> merge_ctx K \<Gamma>1' \<Gamma>2'"

| typing_min_all_empty : "\<Xi>, K, empty n \<turnstile>* [] :m [] \<stileturn> empty n"

| typing_min_all_cons  : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                      ; \<Xi>, K, \<Gamma>1 \<turnstile>  e  :m t \<stileturn> \<Gamma>1'
                      ; \<Xi>, K, \<Gamma>2 \<turnstile>* es :m ts \<stileturn>  \<Gamma>2'
                      \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile>* (e # es) :m (t # ts) \<stileturn> merge_ctx K \<Gamma>1' \<Gamma>2'"

lemma minimal_typing_soundness:
  shows "\<Xi>, K, \<Gamma> \<turnstile> e : t \<Longrightarrow> \<exists>\<Gamma>'. (\<Xi>, K, \<Gamma> \<turnstile> e :m t \<stileturn> \<Gamma>') \<and> (K \<turnstile> \<Gamma> \<leadsto>w  \<Gamma>')"
    and "\<Xi>, K, \<Gamma> \<turnstile>* es : ts \<Longrightarrow> \<exists>\<Gamma>'. (\<Xi>, K, \<Gamma> \<turnstile>* es :m ts \<stileturn> \<Gamma>') \<and> (K \<turnstile> \<Gamma> \<leadsto>w  \<Gamma>')"
proof (induct rule: typing_typing_all.inducts)
  case (typing_var K \<Gamma> i t \<Xi>)
  then show ?case sorry
next
  case (typing_afun \<Xi> f K' t u K ts \<Gamma>)
  then have "\<Xi>, K, \<Gamma> \<turnstile> AFun f ts :m instantiate ts (TFun t u) \<stileturn> Cogent.empty (length \<Gamma>)"
    using typing_min_afun by fast
  then show ?case
    using typing_afun is_consumed_def by blast
next
  case (typing_fun \<Xi> K' t f u K \<Gamma> ts)
  then have "\<Xi>, K, \<Gamma> \<turnstile> Fun f ts :m instantiate ts (TFun t u) \<stileturn> Cogent.empty (length \<Gamma>)"
    using typing_min_fun by fast
  then show ?case
    using typing_fun is_consumed_def by blast
next
  case (typing_app K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> a x y b)
  then show ?case sorry
next
  case (typing_con \<Xi> K \<Gamma> x t tag ts)
  then show ?case sorry
next
  case (typing_cast \<Xi> K \<Gamma> e \<tau> \<tau>')
  then show ?case sorry
next
  case (typing_tuple K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> t T u U)
  then show ?case sorry
next
  case (typing_split K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t u y t')

  obtain \<Gamma>1' TU\<Gamma>2'
    where weakened_subctxs:
      "\<Xi>, K, \<Gamma>1 \<turnstile> x :m TProduct t u \<stileturn> \<Gamma>1'"
      "K \<turnstile> \<Gamma>1 \<leadsto>w \<Gamma>1'"
      "\<Xi>, K, Some t # Some u # \<Gamma>2 \<turnstile> y :m t' \<stileturn> TU\<Gamma>2'"
      "K \<turnstile> Some t # Some u # \<Gamma>2 \<leadsto>w TU\<Gamma>2'"
    using typing_split
    by fast
  then obtain T' U' \<Gamma>2'
    where subctx2_simps:
      "TU\<Gamma>2' = T' # U' # \<Gamma>2'"
      "K \<turnstile> \<Gamma>2 \<leadsto>w \<Gamma>2'"
    by (metis list_all2_Cons1 weakening_def)
  
  obtain \<Gamma>' where weaken_and_split\<Gamma>:
    "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
    "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1' | \<Gamma>2'"
    using weaken_and_split weakened_subctxs subctx2_simps typing_split
    by meson
  then have \<Gamma>'_is: "\<Gamma>' = merge_ctx K \<Gamma>1' \<Gamma>2'"
    by (simp add: merge_ctx_correct weaken_and_split\<Gamma>(2))

  have "\<Xi>, K, \<Gamma> \<turnstile> Split x y :m t' \<stileturn> merge_ctx K \<Gamma>1' \<Gamma>2'"
    using typing_min_split typing_split weakened_subctxs subctx2_simps
    by blast
  then show ?case
    using \<Gamma>'_is weaken_and_split\<Gamma>
    by fast
next
  case (typing_let K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t y u)
  then show ?case sorry
next
  case (typing_letb K "is" \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t y u k)
  then show ?case sorry
next
  case (typing_case K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x ts tag t a u b)
  then show ?case sorry
next
  case (typing_esac \<Xi> K \<Gamma> x ts uu t)
  then show ?case sorry
next
  case (typing_if K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x a t b)
  then show ?case sorry
next
  case (typing_prim \<Xi> K \<Gamma> args ts oper t)
  then show ?case sorry
next
  case (typing_lit K \<Gamma> \<Xi> l)
  then show ?case sorry
next
  case (typing_unit K \<Gamma> \<Xi>)
  then show ?case sorry
next
  case (typing_struct \<Xi> K \<Gamma> es ts)
  then show ?case sorry
next
  case (typing_member \<Xi> K \<Gamma> e ts s k f t)
  then show ?case sorry
next
  case (typing_take K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f t k taken e' u)
  then show ?case sorry
next
  case (typing_put K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f t taken k e')
  then show ?case sorry
next
  case (typing_all_empty \<Xi> K n)
  then show ?case sorry
next
  case (typing_all_cons K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e t es ts)
  then show ?case sorry
qed

lemma minimal_typing_completeness:
  assumes "\<Xi>, K, \<Gamma> \<turnstile> e :m t \<stileturn> \<Gamma>'"
  shows "\<Xi>, K, \<Gamma>' \<turnstile> e : t"
  sorry

lemma minimal_typing_generates_minimal_weakened:
  assumes "\<Xi>, K, \<Gamma> \<turnstile> e :m t \<stileturn> \<Gamma>'"
  shows "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
  and "\<And>\<Gamma>''. \<Xi>, K, \<Gamma>'' \<turnstile> e : t \<Longrightarrow> \<not> (K \<turnstile> \<Gamma>' \<leadsto>w \<Gamma>'')"
  sorry

end
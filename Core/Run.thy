theory Run
  imports Semantics
begin

section \<open>Runs\<close>

text \<open>
  \<^cite>\<open>\<open>Def. 4\<close> in EPTCS69\<close> defines a run \<open>(e\<^sub>0, a\<^sub>0), (e\<^sub>1, a\<^sub>1), \<dots>\<close> of \<open>T(G)\<close> to be
  the sequence of labels of a sequence of transitions \<open>M\<^sub>i \<rightarrow>\<^bsub>(e\<^sub>i, a\<^sub>i)\<^esub> M\<^sub>i\<^sub>+\<^sub>1\<close>, where
  \<open>M\<^sub>i = (Ex\<^sub>i, Re\<^sub>i, In\<^sub>i)\<close> and \<open>M\<^sub>0\<close> is the marking of \<open>G\<close>. Runs may be finite or
  infinite.

  We keep the markings \<open>M\<^sub>i\<close> next to the labels, because acceptance refers to them.
  A finite run is a list of labels together with a list of markings, one longer than the
  list of labels; \<open>Ms ! i\<close> is the marking \<open>M\<^sub>i\<close>. An infinite run is a pair of sequences
  indexed by the natural numbers.
\<close>

subsection \<open>Finite runs\<close>

text \<open>A sequence of transitions \<open>M\<^sub>i \<rightarrow>\<^bsub>(e\<^sub>i, a\<^sub>i)\<^esub> M\<^sub>i\<^sub>+\<^sub>1\<close>, for \<open>i < n\<close>:\<close>

definition transitions ::
    "('event, 'action) dcr_graph \<Rightarrow> ('event \<times> 'action) list \<Rightarrow> 'event marking list \<Rightarrow> bool" where
  "transitions G ls Ms \<longleftrightarrow>
    length Ms = Suc (length ls) \<and> (\<forall>i < length ls. G \<turnstile> Ms ! i \<rightarrow>\<^bsub>ls ! i\<^esub> Ms ! Suc i)"

text \<open>A finite run starts in the marking of the graph.\<close>

definition finite_run ::
    "('event, 'action) dcr_graph \<Rightarrow> ('event \<times> 'action) list \<Rightarrow> 'event marking list \<Rightarrow> bool" where
  "finite_run G ls Ms \<longleftrightarrow> transitions G ls Ms \<and> Ms ! 0 = marking G"

text \<open>
  The same sequences, described one transition at a time. These equations let the
  simplifier check concrete runs.
\<close>

lemma transitions_Nil [simp]: "transitions G [] [M]"
  by (simp add: transitions_def)

lemma transitions_Cons [simp]:
  "transitions G (l # ls) (M # M' # Ms) \<longleftrightarrow> G \<turnstile> M \<rightarrow>\<^bsub>l\<^esub> M' \<and> transitions G ls (M' # Ms)"
  by (auto simp: transitions_def All_less_Suc2)

lemma transitions_length [simp]:
  "transitions G ls [] = False"
  "transitions G (l # ls) [M] = False"
  "transitions G [] (M # M' # Ms) = False"
  by (simp_all add: transitions_def)

text \<open>
  Transitions are deterministic, so the markings of a run are determined by its labels.
  Acceptance therefore does not depend on which markings we consider.
\<close>

lemma transitions_unique:
  assumes "transitions G ls Ms" and "transitions G ls Ms'" and "Ms ! 0 = Ms' ! 0"
  shows "Ms = Ms'"
proof (rule nth_equalityI)
  show "length Ms = length Ms'"
    using assms by (simp add: transitions_def)
  have "Ms ! i = Ms' ! i" if "i \<le> length ls" for i
    using that
  proof (induction i)
    case 0
    show ?case using assms(3) by simp
  next
    case (Suc i)
    then have i: "i < length ls" and IH: "Ms ! i = Ms' ! i"
      by simp_all
    have "G \<turnstile> Ms ! i \<rightarrow>\<^bsub>ls ! i\<^esub> Ms ! Suc i" and "G \<turnstile> Ms' ! i \<rightarrow>\<^bsub>ls ! i\<^esub> Ms' ! Suc i"
      using assms(1,2) i by (simp_all add: transitions_def)
    then show ?case
      using IH step_deterministic by metis
  qed
  then show "Ms ! i = Ms' ! i" if "i < length Ms" for i
    using that assms(1) by (simp add: transitions_def)
qed

lemma finite_run_unique:
  assumes "finite_run G ls Ms" and "finite_run G ls Ms'"
  shows "Ms = Ms'"
  using assms by (auto simp: finite_run_def intro: transitions_unique)

subsection \<open>Infinite runs\<close>

definition infinite_run ::
    "('event, 'action) dcr_graph \<Rightarrow> (nat \<Rightarrow> 'event \<times> 'action) \<Rightarrow> (nat \<Rightarrow> 'event marking) \<Rightarrow> bool" where
  "infinite_run G ls Ms \<longleftrightarrow> Ms 0 = marking G \<and> (\<forall>i. G \<turnstile> Ms i \<rightarrow>\<^bsub>ls i\<^esub> Ms (Suc i))"

lemma infinite_run_unique:
  assumes "infinite_run G ls Ms" and "infinite_run G ls Ms'"
  shows "Ms = Ms'"
proof
  show "Ms i = Ms' i" for i
  proof (induction i)
    case 0
    then show ?case using assms by (simp add: infinite_run_def)
  next
    case (Suc i)
    then show ?case
      using assms step_deterministic by (metis infinite_run_def)
  qed
qed

end

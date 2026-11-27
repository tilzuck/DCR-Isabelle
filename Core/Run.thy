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
  A finite run is therefore a pair of lists, and an infinite run a pair of sequences
  indexed by the natural numbers.
\<close>

subsection \<open>Finite runs\<close>

text \<open>
  A sequence of transitions \<open>M\<^sub>i \<rightarrow>\<^bsub>(e\<^sub>i, a\<^sub>i)\<^esub> M\<^sub>i\<^sub>+\<^sub>1\<close>, for \<open>i < n\<close>, is represented by two
  separate lists:
  \<^item> \<open>ls\<close>, the labels \<open>(e\<^sub>i, a\<^sub>i)\<close> of the transitions, which form the run of the paper;
  \<^item> \<open>Ms\<close>, the markings \<open>M\<^sub>i\<close> that the transitions pass through.

  There is one marking more than there are labels: the label \<open>ls ! i\<close> leads from the
  marking \<open>Ms ! i\<close> to the marking \<open>Ms ! Suc i\<close>. With two lists, \<open>ls\<close> is exactly the
  run of the paper and \<open>Ms ! i\<close> is exactly \<open>M\<^sub>i\<close>. A single list of transitions
  \<open>(M\<^sub>i, (e\<^sub>i, a\<^sub>i), M\<^sub>i\<^sub>+\<^sub>1)\<close> would store every marking in between twice, and would need the
  extra condition that consecutive transitions agree on it. The first marking is not
  fixed here; a finite run, below, starts in the marking of the graph.
\<close>

definition transitions ::
    "('event, 'action) dcr_graph \<Rightarrow> ('event \<times> 'action) list \<Rightarrow> 'event marking list \<Rightarrow> bool" where
  "transitions G ls Ms \<longleftrightarrow>
    length Ms = Suc (length ls) \<and> (\<forall>i < length ls. G \<turnstile> Ms ! i \<rightarrow>\<^bsub>ls ! i\<^esub> Ms ! Suc i)"

text \<open>A sequence of transitions has exactly one marking more than it has labels.\<close>

lemma transitions_length_markings:
  assumes "transitions G ls Ms"
  shows "length Ms = Suc (length ls)"
  using assms by (simp add: transitions_def)

text \<open>A finite run starts in the marking of the graph.\<close>

definition finite_run ::
    "('event, 'action) dcr_graph \<Rightarrow> ('event \<times> 'action) list \<Rightarrow> 'event marking list \<Rightarrow> bool" where
  "finite_run G ls Ms \<longleftrightarrow> transitions G ls Ms \<and> Ms ! 0 = marking G"

text \<open>
  The definition of \<^const>\<open>transitions\<close> speaks about positions in the lists. To check a
  concrete sequence, such as the runs of the examples, it is easier to go through the
  lists one transition at a time, following how lists are built from \<open>[]\<close> and \<open>#\<close>:
  \<^item> \<open>transitions_Nil\<close>: without labels, a single marking is a sequence of transitions,
    whichever marking it is;
  \<^item> \<open>transitions_Cons\<close>: a sequence with a first label \<open>l\<close> is a transition
    \<open>M \<rightarrow>\<^bsub>l\<^esub> M'\<close> from the first marking to the second, followed by a sequence that
    starts in \<open>M'\<close>.

  Both are simplification rules. On a concrete run, the simplifier applies
  \<open>transitions_Cons\<close> once per label, which leaves one transition to check for each, and
  \<open>transitions_Nil\<close> closes the remaining empty sequence. The lemmas
  \<open>transitions_length\<close> let it reject lists whose lengths do not fit together.
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
  show "Ms ! i = Ms' ! i" if "i < length Ms" for i
    using that 
  proof (induction i)
    case 0
    show ?case using assms by simp
  next
   case (Suc i)
    then have i: "i < length ls" and IH: "Ms ! i = Ms' ! i"
      using transitions_length_markings[OF assms(1)] by simp_all
    have "G \<turnstile> Ms ! i \<rightarrow>\<^bsub>ls ! i\<^esub> Ms ! Suc i" and "G \<turnstile> Ms' ! i \<rightarrow>\<^bsub>ls ! i\<^esub> Ms' ! Suc i"
      using assms i by (simp_all add: transitions_def)
    then show ?case 
      using IH step_deterministic by metis
  qed
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

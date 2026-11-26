theory Semantics
  imports DCR_Graph
begin

section \<open>Transitions\<close>

text \<open>
  The execution semantics of a DCR graph \<open>G\<close> is the labelled transition system
  \<open>T(G)\<close> of \<^cite>\<open>\<open>Def. 4\<close> in EPTCS69\<close>. Its states are the markings, its initial state is
  the marking of \<open>G\<close>, and its transitions are labelled with an event \<open>e\<close> and an action \<open>a\<close>.
  A transition \<open>M' \<rightarrow>\<^bsub>(e, a)\<^esub> M''\<close> exists iff
  \<^item> (i) \<open>M' = (Ex', Re', In')\<close> is the marking before the transition,
  \<^item> (ii) \<open>M'' = (Ex' \<union> {e}, Re'', In'')\<close> is the marking after the transition,
  \<^item> (iii) \<open>e \<in> In'\<close> and \<open>l(e) = a\<close>,
  \<^item> (iv) \<open>{e' \<in> In' | e' \<rightarrow>\<bullet> e} \<subseteq> Ex'\<close>,
  \<^item> (v) \<open>In'' = (In' \<union> {e' | e \<rightarrow>+ e'}) \ {e' | e \<rightarrow>% e'}\<close>,
  \<^item> (vi) \<open>Re'' = (Re' \ {e}) \<union> {e' | e \<bullet>\<rightarrow> e'}\<close>.
\<close>

text \<open>
  In words: only an included event can be executed (iii), and only if all its included
  conditions have been executed before (iv). Executing it records it as executed (ii),
  updates the included events (v), and replaces it as a pending response by its own
  responses (vi).

  In (v), an event that is both included and excluded by \<open>e\<close> ends up excluded. This case
  cannot arise in the paper, where \<open>\<plusminus>\<close> is a partial map, but it can for
  \<^typ>\<open>('event, 'action) dcr_graph\<close>. The formalisation of Christfort and Debois
  \<^cite>\<open>AFP23\<close> resolves it the other way round, with \<open>(In' \ {e' | e \<rightarrow>% e'}) \<union> {e' | e \<rightarrow>+ e'}\<close>,
  as do the later papers. Both updates agree on graphs with
  \<open>inclusion_exclusion_disjoint\<close>.
\<close>

text \<open>
  The transition relation is defined item by item. The graph is written in front, as in
  \<open>G \<turnstile> M' \<rightarrow>\<^bsub>(e, a)\<^esub> M''\<close>, because the paper's \<open>T(G)\<close> depends on it. Item (i) only names
  the components of \<open>M'\<close>, which are \<open>Ex M'\<close>, \<open>Re M'\<close> and \<open>In M'\<close> here.
\<close>

fun step ::
    "('event, 'action) dcr_graph \<Rightarrow> 'event marking \<Rightarrow> 'event \<times> 'action \<Rightarrow> 'event marking \<Rightarrow> bool"
    (\<open>(_ \<turnstile> _ \<rightarrow>\<^bsub>_\<^esub> _)\<close> [51, 51, 0, 51] 50)
  where "G \<turnstile> M' \<rightarrow>\<^bsub>(e, a)\<^esub> M'' \<longleftrightarrow>
      Ex M'' = Ex M' \<union> {e}                                              \<comment> \<open>(ii)\<close>
    \<and> e \<in> In M' \<and> label G e = a                                         \<comment> \<open>(iii)\<close>
    \<and> {e' \<in> In M'. e' \<rightarrow>\<bullet>\<^bsub>G\<^esub> e} \<subseteq> Ex M'                                \<comment> \<open>(iv)\<close>
    \<and> In M'' = (In M' \<union> {e'. e \<rightarrow>+\<^bsub>G\<^esub> e'}) - {e'. e \<rightarrow>%\<^bsub>G\<^esub> e'}      \<comment> \<open>(v)\<close>
    \<and> Re M'' = (Re M' - {e}) \<union> {e'. e \<bullet>\<rightarrow>\<^bsub>G\<^esub> e'}"                \<comment> \<open>(vi)\<close>

subsection \<open>Enabled events and their execution\<close>

text \<open>
  Items (iii) and (iv) only concern \<open>M'\<close>: they say when an event can be executed. Items (ii),
  (v) and (vi) determine \<open>M''\<close> from \<open>M'\<close> and \<open>e\<close>. We name the two parts.
\<close>

definition enabled :: "('event, 'action) dcr_graph \<Rightarrow> 'event marking \<Rightarrow> 'event \<Rightarrow> bool" where
  "enabled G M e \<longleftrightarrow> e \<in> In M \<and> {e' \<in> In M. e' \<rightarrow>\<bullet>\<^bsub>G\<^esub> e} \<subseteq> Ex M"

definition execute :: "('event, 'action) dcr_graph \<Rightarrow> 'event marking \<Rightarrow> 'event \<Rightarrow> 'event marking" where
  "execute G M e =
    \<lparr>Ex = Ex M \<union> {e},
     Re = (Re M - {e}) \<union> {e'. e \<bullet>\<rightarrow>\<^bsub>G\<^esub> e'},
     In = (In M \<union> {e'. e \<rightarrow>+\<^bsub>G\<^esub> e'}) - {e'. e \<rightarrow>%\<^bsub>G\<^esub> e'}\<rparr>"

text \<open>
  A transition is exactly an enabled event, executed, with its label as the action. Most
  proofs use this form.
\<close>

lemma step_iff:
  "G \<turnstile> M' \<rightarrow>\<^bsub>(e, a)\<^esub> M'' \<longleftrightarrow> enabled G M' e \<and> a = label G e \<and> M'' = execute G M' e"
  by (auto simp: enabled_def execute_def)


subsection \<open>Basic properties\<close>

text \<open>The marking after a transition is determined by the marking before it and the label.\<close>

lemma step_deterministic:
  assumes "G \<turnstile> M \<rightarrow>\<^bsub>ea\<^esub> M\<^sub>1" and "G \<turnstile> M \<rightarrow>\<^bsub>ea\<^esub> M\<^sub>2"
  shows "M\<^sub>1 = M\<^sub>2"
  using assms by (cases ea) (simp add: step_iff)

text \<open>Executed events stay executed.\<close>

lemma step_executed_mono:
  assumes "G \<turnstile> M \<rightarrow>\<^bsub>ea\<^esub> M'"
  shows "Ex M \<subseteq> Ex M'"
  using assms by (cases ea) auto

text \<open>An event stops being pending only by being executed.\<close>

lemma step_pending_resolved:
  assumes "G \<turnstile> M \<rightarrow>\<^bsub>(e, a)\<^esub> M'" and "e' \<in> Re M" and "e' \<notin> Re M'"
  shows "e' = e"
  using assms by auto

text \<open>
  A graph with finitely many events has finitely many markings, so \<open>T(G)\<close> is a finite
  transition system.
\<close>

lemma finite_markings:
  assumes "finite (UNIV :: 'event set)"
  shows "finite (UNIV :: 'event marking set)"
proof -
  let ?triple = "\<lambda>(x, y, z). \<lparr>Ex = x, Re = y, In = z\<rparr>"
  have "M \<in> range ?triple" for M :: "'event marking"
    by (rule image_eqI[of M _ "(Ex M, Re M, In M)"]) (auto intro: marking.equality)
  then have u:"(UNIV :: 'event marking set) = range ?triple"
    by blast
  moreover have f:"finite (UNIV :: ('event set \<times> 'event set \<times> 'event set) set)"
    using assms by (simp add: finite_Prod_UNIV Finite_Set.finite_set)
  ultimately show ?thesis
    by (simp add: u f)
qed

end

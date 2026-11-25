theory DCR_Graph
  imports Marking
begin

section \<open>DCR graphs\<close>

text \<open>
  A \<^emph>\<open>dynamic condition response graph\<close> (DCR graph), originally introduced in
  \<^cite>\<open>\<open>Def. 3\<close> in EPTCS69\<close>, is a tuple \<open>G = (E, M, Act, \<rightarrow>\<bullet>, \<bullet>\<rightarrow>, \<plusminus>, l)\<close> where
  \<^item> (i) \<open>E\<close> is the set of events,
  \<^item> (ii) \<open>M = (Ex, Re, In)\<close> is the marking,
  \<^item> (iii) \<open>Act\<close> is the set of actions,
  \<^item> (iv) \<open>\<rightarrow>\<bullet> \<subseteq> E \<times> E\<close> is the condition relation,
  \<^item> (v) \<open>\<bullet>\<rightarrow> \<subseteq> E \<times> E\<close> is the response relation,
  \<^item> (vi) \<open>\<plusminus> : E \<times> E \<rightharpoonup> {+, %}\<close> defines the dynamic inclusion and exclusion
    relations \<open>\<rightarrow>+\<close> and \<open>\<rightarrow>%\<close>,
  \<^item> (vii) \<open>l : E \<rightarrow> Act\<close> is the labelling function.
\<close>

text \<open>
  We adopt the definition of the existing Isabelle formalisation of DCR graphs by Christfort
  and Debois \<^cite>\<open>AFP23\<close>: the marking is a record with the fields \<open>Ex\<close>, \<open>Re\<close> and \<open>In\<close>,
  and each relation is a set of pairs of events, in the same direction. Unlike there, the
  events are a type variable rather than natural numbers with an explicit set of events,
  graphs carry the labelling (vii), and there is no milestone relation, which only appears
  in later papers.

  Implementation notes:
  \<^item> The set of events (i) and the set of actions (iii) are the type variables
    \<^typ>\<open>'event\<close> and \<^typ>\<open>'action\<close>.
  \<^item> The relations are sets of pairs, \<^typ>\<open>'event rel\<close>, exactly as
    \<open>\<rightarrow>\<bullet> \<subseteq> E \<times> E\<close> in the paper.
  \<^item> The partial map \<open>\<plusminus>\<close> (vi) is split into two relations, \<open>inclusion\<close> and
    \<open>exclusion\<close>, as in all later papers. The field names are the paper's
    words, the "dynamic inclusion/exclusion relations"; \<^verbatim>\<open>include\<close> and
    \<^verbatim>\<open>includes\<close> are Isabelle keywords. Because \<open>\<plusminus>\<close> is a partial map, the paper
    never has an event that both includes and excludes the same event. We do not
    impose this restriction; it is the property \<open>inclusion_exclusion_disjoint\<close>.
  \<^item> The marking (ii) is the marking the graph starts in. The semantics (Def. 4) works
    with arbitrary markings.
\<close>

record ('event, 'action) dcr_graph =
  marking :: "'event marking"
  condition :: "'event rel"
  response :: "'event rel"
  inclusion :: "'event rel"
  exclusion :: "'event rel"
  label :: "'event \<Rightarrow> 'action"

subsection \<open>Notation\<close>

text \<open>
  The relations are written with the paper's arrows, the graph as a subscript:
  \<^item> \<open>e \<rightarrow>\<bullet>\<^bsub>G\<^esub> e'\<close>: \<open>e\<close> is a condition for \<open>e'\<close>. While \<open>e\<close> is included, \<open>e'\<close> can only
    be executed if \<open>e\<close> has been executed.
  \<^item> \<open>e \<bullet>\<rightarrow>\<^bsub>G\<^esub> e'\<close>: \<open>e'\<close> is a response to \<open>e\<close>. Executing \<open>e\<close> makes \<open>e'\<close> pending, so
    \<open>e'\<close> must later be executed or excluded.
  \<^item> \<open>e \<rightarrow>+\<^bsub>G\<^esub> e'\<close>: \<open>e\<close> includes \<open>e'\<close>. Executing \<open>e\<close> includes \<open>e'\<close>.
  \<^item> \<open>e \<rightarrow>%\<^bsub>G\<^esub> e'\<close>: \<open>e\<close> excludes \<open>e'\<close>. Executing \<open>e\<close> excludes \<open>e'\<close>.
\<close>

text \<open>
  They are abbreviations for memberships such as \<open>(e, e') \<in> condition G\<close>, and Isabelle
  prints such memberships with the arrows.
\<close>

abbreviation condition_arrow :: "'event \<Rightarrow> ('event, 'action) dcr_graph \<Rightarrow> 'event \<Rightarrow> bool"
    (\<open>(_ \<rightarrow>\<bullet>\<^bsub>_\<^esub> _)\<close> [51, 0, 51] 50)
  where "e \<rightarrow>\<bullet>\<^bsub>G\<^esub> e' \<equiv> (e, e') \<in> condition G"

abbreviation response_arrow :: "'event \<Rightarrow> ('event, 'action) dcr_graph \<Rightarrow> 'event \<Rightarrow> bool"
    (\<open>(_ \<bullet>\<rightarrow>\<^bsub>_\<^esub> _)\<close> [51, 0, 51] 50)
  where "e \<bullet>\<rightarrow>\<^bsub>G\<^esub> e' \<equiv> (e, e') \<in> response G"

abbreviation inclusion_arrow :: "'event \<Rightarrow> ('event, 'action) dcr_graph \<Rightarrow> 'event \<Rightarrow> bool"
    (\<open>(_ \<rightarrow>+\<^bsub>_\<^esub> _)\<close> [51, 0, 51] 50)
  where "e \<rightarrow>+\<^bsub>G\<^esub> e' \<equiv> (e, e') \<in> inclusion G"

abbreviation exclusion_arrow :: "'event \<Rightarrow> ('event, 'action) dcr_graph \<Rightarrow> 'event \<Rightarrow> bool"
    (\<open>(_ \<rightarrow>%\<^bsub>_\<^esub> _)\<close> [51, 0, 51] 50)
  where "e \<rightarrow>%\<^bsub>G\<^esub> e' \<equiv> (e, e') \<in> exclusion G"

subsection \<open>The restriction implicit in \<open>\<plusminus>\<close>\<close>

text \<open>
  No event both includes and excludes the same event, i.e. \<open>\<rightarrow>+ \<inter> \<rightarrow>% = {}\<close>. In
  \<^cite>\<open>\<open>Def. 3 (vi)\<close> in EPTCS69\<close> this holds automatically, because \<open>\<plusminus>\<close> is a partial map.
  \<^typ>\<open>('event, 'action) dcr_graph\<close> does not require it.
\<close>

definition inclusion_exclusion_disjoint :: "('event, 'action) dcr_graph \<Rightarrow> bool" where
  "inclusion_exclusion_disjoint G \<longleftrightarrow> inclusion G \<inter> exclusion G = {}"

end

theory Prescribe_Medicine_With_Check
  imports DCR_Graph
begin

section \<open>The prescribe-medicine example with check\<close>

text \<open>
  The graph of \<^cite>\<open>\<open>Fig. 3(b)\<close> in EPTCS69\<close>: the prescribe-medicine example of
  Fig. 3(a), with an extra event \<^emph>\<open>don't trust\<close>, with which the nurse indicates distrust of the prescription. Each
  relation is written as the set of its arrows.
\<close>

text \<open>
  \<^latex>\<open>
  \begin{center}
  \begin{dcrgraph}
    \activity[role=D]{prescribe medicine}{pm}
    \activity[role=D, below=2cm of pm]{sign}{s}
    \activity[role=N, right=3cm of pm]{give medicine}{gm}
    \activity[role=N, right=3cm of s]{don't trust}{dt}
    \condition{pm}{s}
    \response{pm}{s}
    \response{pm}{gm}
    \condition{s}{gm}
    \include{s}{gm}
    \condition{s}{dt}
    \include{s}{dt}
    \response{dt}{s}
    \exclude{gm}{dt}
    \exclude{dt}{gm}
  \end{dcrgraph}
  \end{center}\<close>
\<close>

datatype event =
  Prescribe  \<comment> \<open>\<^emph>\<open>prescribe medicine\<close>, by a doctor (labelled "ordinate medicine" in the figure)\<close>
| Sign       \<comment> \<open>\<^emph>\<open>sign\<close>, by a doctor\<close>
| Give       \<comment> \<open>\<^emph>\<open>give medicine\<close>, by a nurse\<close>
| DontTrust  \<comment> \<open>\<^emph>\<open>don't trust\<close>, by a nurse\<close>

text \<open>The marking is the same as in Fig. 3(a): nothing executed, nothing pending, all
  events included.\<close>

definition prescribe_medicine_with_check :: "(event, string) dcr_graph" where
  "prescribe_medicine_with_check =
    \<lparr>marking = \<lparr>Ex = {}, Re = {}, In = UNIV\<rparr>,
     condition = {(Prescribe, Sign), (Sign, Give), (Sign, DontTrust)},
     response = {(Prescribe, Sign), (Prescribe, Give), (DontTrust, Sign)},
     inclusion = {(Sign, Give), (Sign, DontTrust)},
     exclusion = {(Give, DontTrust), (DontTrust, Give)},
     label = (\<lambda>e. case e of
        Prescribe \<Rightarrow> ''prescribe medicine''
      | Sign \<Rightarrow> ''sign''
      | Give \<Rightarrow> ''give medicine''
      | DontTrust \<Rightarrow> ''don't trust'')\<rparr>"

text \<open>\<open>Give\<close> and \<open>DontTrust\<close> exclude each other.\<close>

lemma "Give \<rightarrow>%\<^bsub>prescribe_medicine_with_check\<^esub> DontTrust
     \<and> DontTrust \<rightarrow>%\<^bsub>prescribe_medicine_with_check\<^esub> Give"
  by (simp add: prescribe_medicine_with_check_def)

text \<open>Executing \<open>Sign\<close> includes exactly \<open>Give\<close> and \<open>DontTrust\<close>.\<close>

lemma "{e. Sign \<rightarrow>+\<^bsub>prescribe_medicine_with_check\<^esub> e} = {Give, DontTrust}"
  by (auto simp: prescribe_medicine_with_check_def)

text \<open>The graph satisfies the restriction implicit in Def. 3 (vi): \<open>\<rightarrow>+ \<inter> \<rightarrow>% = {}\<close>.\<close>

lemma "inclusion_exclusion_disjoint prescribe_medicine_with_check"
  by (auto simp: inclusion_exclusion_disjoint_def prescribe_medicine_with_check_def)

end

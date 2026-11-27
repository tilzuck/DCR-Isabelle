theory Prescribe_Medicine
  imports Run
begin

section \<open>The prescribe-medicine example\<close>

text \<open>
  The graph of \<^cite>\<open>\<open>Fig. 3(a)\<close> in EPTCS69\<close>, taken from a field study of oncology
  workflow at Danish hospitals: a doctor \<^emph>\<open>prescribes medicine\<close> and \<^emph>\<open>signs\<close> the prescription, and a nurse
  \<^emph>\<open>gives the medicine\<close>. Each relation is written as the set of its arrows.
  The roles D (doctor) and N (nurse) are those of the figure; they enter the formalisation
  with distributed graphs (Def. 5).
\<close>

text \<open>
  \<^latex>\<open>
  \begin{center}
  \begin{dcrgraph}
    \activity[role=D]{prescribe medicine}{pm}
    \activity[role=D, below=2cm of pm]{sign}{s}
    \activity[role=N, right=3cm of pm]{give medicine}{gm}
    \condition{pm}{s}
    \response{pm}{s}
    \response{pm}{gm}
    \condition{s}{gm}
  \end{dcrgraph}
  \end{center}\<close>
\<close>

datatype event =
  Prescribe  \<comment> \<open>\<^emph>\<open>prescribe medicine\<close>, by a doctor\<close>
| Sign       \<comment> \<open>\<^emph>\<open>sign\<close>, by a doctor\<close>
| Give       \<comment> \<open>\<^emph>\<open>give medicine\<close>, by a nurse\<close>

text \<open>In the marking, nothing has been executed, nothing is pending, and all events are
  included.\<close>

definition prescribe_medicine :: "(event, string) dcr_graph" where
  "prescribe_medicine =
    \<lparr>marking = \<lparr>Ex = {}, Re = {}, In = UNIV\<rparr>,
     condition = {(Prescribe, Sign), (Sign, Give)},
     response = {(Prescribe, Sign), (Prescribe, Give)},
     inclusion = {},
     exclusion = {},
     label = (\<lambda>e. case e of
        Prescribe \<Rightarrow> ''prescribe medicine''
      | Sign \<Rightarrow> ''sign''
      | Give \<Rightarrow> ''give medicine'')\<rparr>"

text \<open>\<open>Prescribe\<close> and \<open>Sign\<close> are related by both a condition and a response.\<close>

lemma "Prescribe \<rightarrow>\<bullet>\<^bsub>prescribe_medicine\<^esub> Sign \<and> Prescribe \<bullet>\<rightarrow>\<^bsub>prescribe_medicine\<^esub> Sign"
  by (simp add: prescribe_medicine_def)

text \<open>\<open>Sign\<close> is the only condition of \<open>Give\<close>.\<close>

lemma "{e. e \<rightarrow>\<bullet>\<^bsub>prescribe_medicine\<^esub> Give} = {Sign}"
  by (auto simp: prescribe_medicine_def)

text \<open>There are no include or exclude arrows.\<close>

lemma "\<not> e \<rightarrow>+\<^bsub>prescribe_medicine\<^esub> e' \<and> \<not> e \<rightarrow>%\<^bsub>prescribe_medicine\<^esub> e'"
  by (simp add: prescribe_medicine_def)

subsection \<open>Transitions\<close>

text \<open>In the initial marking, only \<open>Prescribe\<close> is enabled: \<open>Sign\<close> and \<open>Give\<close> wait for
  their conditions.\<close>

lemma "{e. enabled prescribe_medicine (marking prescribe_medicine) e} = {Prescribe}"
proof (rule set_eqI)
  fix e
  show "e \<in> {e. enabled prescribe_medicine (marking prescribe_medicine) e} \<longleftrightarrow> e \<in> {Prescribe}"
    by (cases e) (auto simp: enabled_def prescribe_medicine_def)
qed

text \<open>Executing \<open>Prescribe\<close> makes \<open>Sign\<close> and \<open>Give\<close> pending.\<close>

lemma "prescribe_medicine \<turnstile> marking prescribe_medicine \<rightarrow>\<^bsub>(Prescribe, ''prescribe medicine'')\<^esub>
    \<lparr>Ex = {Prescribe}, Re = {Sign, Give}, In = UNIV\<rparr>"
  by (auto simp: prescribe_medicine_def)

subsection \<open>Runs\<close>

text \<open>The doctor prescribes and signs, then the nurse gives the medicine. Afterwards
  nothing is pending.\<close>

lemma "finite_run prescribe_medicine
    [(Prescribe, ''prescribe medicine''), (Sign, ''sign''), (Give, ''give medicine'')]
    [\<lparr>Ex = {}, Re = {}, In = UNIV\<rparr>,
     \<lparr>Ex = {Prescribe}, Re = {Sign, Give}, In = UNIV\<rparr>,
     \<lparr>Ex = {Prescribe, Sign}, Re = {Give}, In = UNIV\<rparr>,
     \<lparr>Ex = {Prescribe, Sign, Give}, Re = {}, In = UNIV\<rparr>]"
  by (auto simp: finite_run_def prescribe_medicine_def)

text \<open>\<open>Prescribe\<close> has no conditions, so the doctor can prescribe forever. In this infinite
  run, \<open>Sign\<close> and \<open>Give\<close> stay pending from the first step on.\<close>

lemma "infinite_run prescribe_medicine
    (\<lambda>i. (Prescribe, ''prescribe medicine''))
    (\<lambda>i. if i = 0 then \<lparr>Ex = {}, Re = {}, In = UNIV\<rparr>
         else \<lparr>Ex = {Prescribe}, Re = {Sign, Give}, In = UNIV\<rparr>)"
  by (auto simp: infinite_run_def prescribe_medicine_def)

end

theory Marking
  imports Main
begin

section \<open>Markings\<close>

text \<open>
  A \<^emph>\<open>marking\<close> \<open>M = (Ex, Re, In)\<close> is the run-time state of a DCR graph
  \<^cite>\<open>\<open>Def. 3 (ii)\<close> in EPTCS69\<close>. It consists of three sets of events:
  \<^item> \<open>Ex\<close>, the events that have been executed;
  \<^item> \<open>Re\<close>, the pending responses: events that must eventually be executed or excluded;
  \<^item> \<open>In\<close>, the events that are currently included.

  The type of events is the type variable \<^typ>\<open>'event\<close>: every element of
  \<^typ>\<open>'event\<close> is an event. The fields carry the paper's names.
\<close>

record 'event marking =
  Ex :: "'event set"
  Re :: "'event set"
  In :: "'event set"

end

theory Mizar_By
imports Mizar
begin

ML {*
structure Miz_Auto_Data = Generic_Data
( type T = thm Item_Net.T;
  val empty = Thm.full_rules;
  val extend = I;
  val merge = Item_Net.merge);
*}
ML {*
fun add_thm thm ctxt = Miz_Auto_Data.map (Item_Net.update thm) ctxt;
fun del_thm thm ctxt = Miz_Auto_Data.map (Item_Net.remove thm) ctxt;
fun add_or_del aod_fn = Thm.declaration_attribute (fn thm => fn ctxt => aod_fn thm ctxt);
val attrib = Attrib.add_del (add_or_del add_thm) (add_or_del del_thm)
*}
setup {* Attrib.setup @{binding "miz"} attrib "Declare as Mizar automation" *}
setup {* Global_Theory.add_thms_dynamic (@{binding "mizs"}, (Item_Net.content o Miz_Auto_Data.get)) *}

end

(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Specialised_Lemma_Utils
imports Utils
begin

text{* This theory file contains utility functions that are specific to the generation and proof of
 the specialised lemmas.
*}

ML{* datatype bucket =
  TakeBoxed
| TakeUnboxed
| PutBoxed
| LetPutBoxed
| PutUnboxed
| MemberBoxed
| MemberReadOnly
| TagDef
| Esac
| Case
| ValRelSimp
| IsValidSimp
| TypeRelSimp
| HeapSimp *}

ML{* fun bucket_to_string bucket = case bucket of
  TakeBoxed   => "TakeBoxed"
| TakeUnboxed => "TakeUnboxed"
| PutBoxed    => "PutBoxed"
| LetPutBoxed => "LetPutBoxed"
| PutUnboxed  => "PutUnboxed"
| MemberBoxed => "MemberBoxed"
| MemberReadOnly => "MemberReadOnly"
| TagDef      => "TagDef"
| Esac        => "Esac"
| Case        => "Case"
| ValRelSimp  => "ValRelSimp"
| IsValidSimp => "IsValidSimp"
| TypeRelSimp => "TypeRelSimp"
| HeapSimp    => "HeapSimp"
*}

ML{* structure Unborn_Thms = Proof_Data
(* Unborn_Thms is a list of thm-names which I tried to prove but failed to do so.
 * Note that I do not include thm-names if I tried to cheat.*)
 (type T = string list;
  fun init _ = [];)
*}

ML{* fun add_unborns unborn_thm = Unborn_Thms.map (fn unborn_thms => unborn_thm::unborn_thms); *}

text{* Lemma buckets. *}

ML {* structure TakeBoxed = Named_Thms_Ext
 (val name = @{binding "TakeBoxed"}
  val description = "Theorems for boxed takes.") *}

ML {* structure TakeUnboxed = Named_Thms_Ext
 (val name = @{binding "TakeUnboxed"}
  val description = "Theorems for unboxed takes.") *}

ML {* structure PutBoxed = Named_Thms_Ext
 (val name = @{binding "PutBoxed"}
  val description = "Theorems for boxed puts.") *}

ML {* structure LetPutBoxed = Named_Thms_Ext
 (val name = @{binding "LetPutBoxed"}
  val description = "Theorems for boxed let-puts.") *}

ML {* structure PutUnboxed = Named_Thms_Ext
 (val name = @{binding "PutUnboxed"}
  val description = "Theorems for unboxed puts.") *}

ML {* structure MemberReadOnly = Named_Thms_Ext
 (val name = @{binding "MemberReadOnly"}
  val description = "Theorems for read-only member.") *}

ML {* structure MemberBoxed = Named_Thms_Ext
 (val name = @{binding "MemberBoxed"}
  val description = "Theorems for boxed member.") *}

ML {* structure Case = Named_Thms_Ext
 (val name = @{binding "Case"}
  val description = "Theorems for case.") *}

ML {* structure ValRelSimp = Named_Thms_Ext
 (val name = @{binding "ValRelSimp"}
  val description = "Simplification rules about value relation.") *}

ML {* structure IsValidSimp = Named_Thms_Ext
 (val name = @{binding "IsValidSimp"}
  val description = "Simplification rules about is_valid.") *}

ML {* structure TypeRelSimp = Named_Thms_Ext
 (val name = @{binding "TypeRelSimp"}
  val description = "Simplification rules about type relation.") *}

ML {* structure HeapSimp = Named_Thms_Ext
 (val name = @{binding "HeapSimp"}
  val description = "Simplification rules about heap relation.") *}

setup{* (* Set up lemma buckets.*)
 TakeBoxed.setup o TakeUnboxed.setup o PutUnboxed.setup o PutBoxed.setup o
 MemberReadOnly.setup o MemberBoxed.setup o Case.setup o
 ValRelSimp.setup o IsValidSimp.setup o
 TypeRelSimp.setup o HeapSimp.setup *}

ML{* fun local_setup_add_thm bucket thm = case bucket of
  TakeBoxed     => TakeBoxed.add_local thm
| TakeUnboxed   => TakeUnboxed.add_local thm
| PutBoxed      => PutBoxed.add_local thm
| LetPutBoxed   => LetPutBoxed.add_local thm
| PutUnboxed    => PutUnboxed.add_local thm
| MemberBoxed   => MemberBoxed.add_local thm
| MemberReadOnly=> MemberReadOnly.add_local thm
| ValRelSimp    => ValRelSimp.add_local thm
| IsValidSimp   => IsValidSimp.add_local thm
| TypeRelSimp   => TypeRelSimp.add_local thm
| HeapSimp      => HeapSimp.add_local thm
| Case          => Case.add_local thm
| _             => error "add_thm in Value_Relation_Generation.thy failed."
*}

ML{* fun setup_add_thm bucket thm = case bucket of
  TakeBoxed     => TakeBoxed.add_thm thm   |> Context.theory_map
| TakeUnboxed   => TakeUnboxed.add_thm thm |> Context.theory_map
| PutBoxed      => PutBoxed.add_thm thm    |> Context.theory_map
| LetPutBoxed   => LetPutBoxed.add_thm thm |> Context.theory_map
| PutUnboxed    => PutUnboxed.add_thm thm  |> Context.theory_map
| MemberBoxed   => MemberBoxed.add_thm thm |> Context.theory_map
| MemberReadOnly=> MemberReadOnly.add_thm thm |> Context.theory_map
| Case          => Case.add_thm thm        |> Context.theory_map
| ValRelSimp    => ValRelSimp.add_thm thm  |> Context.theory_map
| IsValidSimp   => IsValidSimp.add_thm thm |> Context.theory_map
| TypeRelSimp   => TypeRelSimp.add_thm thm |> Context.theory_map
| HeapSimp      => HeapSimp.add_thm thm    |> Context.theory_map
| _             => error "add_thm in SpecialisedLemmaForTakePut.thy failed."
*}

ML{* val local_setup_put_lemmas_in_bucket =
  let
    fun note (name:string) (getter) lthy = Local_Theory.note ((Binding.make (name, @{here}), []), getter lthy) lthy |> snd;
  in
    note "type_rel_simp" TypeRelSimp.get #>
    note "val_rel_simp" ValRelSimp.get #>
    note "take_boxed" TakeBoxed.get #>
    note "take_unboxed" TakeUnboxed.get #>
    note "put_boxed" PutBoxed.get #>
    note "let_put_boxed" LetPutBoxed.get #>
    note "put_unboxed" PutUnboxed.get #>
    note "member_boxed" MemberBoxed.get #>
    note "member_readonly" MemberReadOnly.get #>
    note "case" Case.get #>
    note "is_valid_simp" IsValidSimp.get #>
    note "heap_simp" HeapSimp.get
  end;
*}

ML{* type lem = { name: string, bucket: bucket, prop: term, mk_tactic: Proof.context -> tactic }; *}

ML{* val cheat_specialised_lemmas =
 Attrib.setup_config_bool @{binding "cheat_specialised_lemmas"} (K false);
*}
(* An example to show how to manupulate this flag.*)
declare [[ cheat_specialised_lemmas = false ]]

ML{* (* type definition on the ML-level.*)
datatype sigil = ReadOnly | Writable | Unboxed
datatype uval = UProduct of string
              | USum of string * term (* term contains argument to TSum (excluding TSum itself) *)
              | URecord of string * sigil
              | UAbstract of string;
;
type uvals = uval list;*}

ML{* (* unify_sigils to remove certain kind of duplication.*)
fun unify_sigils (URecord (ty_name,_)) = URecord (ty_name,Writable)
  | unify_sigils uval                  = uval
  (* value-relations and type-relations are independent of sigils.
   * If we have multiple uvals with different sigils but with the same type and name,
   * we should count them as one to avoid trying to instantiate the same thing multiple times.*)
*}

ML{* (* unify_usum_tys *)
fun unify_usum_tys (USum (ty_name,_)) = USum (ty_name, Term.dummy)
  | unify_usum_tys uval               = uval
*}

ML{* (* unify_uabstract *)
fun unify_uabstract (UAbstract _) = UAbstract "dummy"
 |  unify_uabstract uval          = uval;
*}

ML{* (* get_usums, get_uproducts, get_urecords *)
fun get_usums uvals = filter (fn uval => case uval of  (USum _) => true | _ => false) uvals
fun get_uproducts uvals = filter (fn uval => case uval of  (UProduct _) => true | _ => false) uvals
fun get_urecords uvals = filter (fn uval => case uval of  (URecord _) => true | _ => false) uvals
*}

ML{* (* get_uval_name *)
fun get_uval_name (URecord (ty_name, _)) = ty_name
 |  get_uval_name (USum    (ty_name, _)) = ty_name
 |  get_uval_name (UProduct ty_name) = ty_name
 |  get_uval_name (UAbstract ty_name) = ty_name
*}

ML{* fun get_uval_names uvals = map get_uval_name uvals;*}

ML{* (* get_uval_sigil *)
fun get_uval_sigil (URecord (_, sigil)) = sigil
 |  get_uval_sigil _ = error "get_uval_sigil failed. The tyep of this argument is not URecord."
*}

ML{* val get_uval_writable_records =
 filter (fn uval => case uval of (URecord (_, Writable)) => true | _ => false);
*}

ML{* val get_uval_unbox_records =
 filter (fn uval => case uval of (URecord (_, Unboxed)) => true | _ => false);
*}

ML{* val get_uval_readonly_records =
 filter (fn uval => case uval of (URecord (_, ReadOnly)) => true | _ => false);
*}

ML{* fun usum_list_of_types ctxt uval = case uval of
    USum (_, variants) => HOLogic.dest_list variants
  | _ => error ("usum_list_of_types: not USum")
*}

ML{* fun is_UAbstract (UAbstract _) = true
      |  is_UAbstract  _            = false;
*}

ML{* fun get_ty_nm_C uval = uval |> get_uval_name |> (fn nm => nm ^ "_C"); *}

ML{* fun heap_info_uval_to_struct_info (heap:HeapLiftBase.heap_info) (uval:uval) =
 let
  val uval_C_nm = get_uval_name uval ^ "_C";
 in
  Symtab.lookup (#structs heap) uval_C_nm
  |> Utils.the' ("This heap_info does not have structs." ^ uval_C_nm)
 end : HeapLiftBase.struct_info;
*}

ML{* fun heap_info_uval_to_field_names heap_info uval =
 heap_info_uval_to_struct_info heap_info uval |> #field_info |> map #name;
*}

ML{* fun heap_info_uval_to_field_types heap_info uval =
 heap_info_uval_to_struct_info heap_info uval |> #field_info |> map #field_type;
*}

text{* The functions related to AutoCorres.*}

ML{* fun ac_mk_struct_info_for file_nm thy uval =
(* checks if autocorres generates struct_info for a given uval. Returns a boolean value.*)
 let
  val st_C_nm   = get_ty_nm_C uval;
  val heap_info = Symtab.lookup (HeapInfo.get thy) file_nm
                 |> Utils.the' "heap_info in ac_mk_struct_info_for failed."
                 |> #heap_info;
  val flag      = Symtab.lookup (#structs heap_info) st_C_nm |> is_some;
 in flag end;
*}

ML{* fun get_uvals_for_which_ac_mk_st_info file_nm thy uvals =
 (* returns a list of uvals for which autocorres creates struct info.*)
 filter (ac_mk_struct_info_for file_nm thy) uvals;
*}

ML{* fun get_uvals_for_which_ac_mk_heap_getters file_nm thy uvals =
 (* returns a list of uvals for which autocorres creates #heap_getters info.*)
 filter (fn uval => ac_mk_heap_getters_for file_nm thy (get_ty_nm_C uval)) uvals;
*}
end

%{
  let is_uppercase s = s <> "" && s.[0] <> Char.lowercase s.[0];;
  open Tptp;;
%}

%token <string> Word
%token <string list> All
%token <string list> Ex
%token Eof Openp Closep Dot Comma Eq Neq Tilde Eqvt Neqvt Impl Revimpl And Or

%right Impl
%nonassoc Eqvt
%nonassoc Eq Neq
%right Or
%left And
%nonassoc Tilde
%nonassoc All Exists

%start fof_top
%type <(string * string * Tptp.form)> fof_top
%%

fof_top :
  Word Openp Word Comma Word Comma formula Closep Dot { var_num := 0; Hashtbl.clear var_no; Hashtbl.clear no_var; ($3, $5, $7) }
| Eof { raise End_of_file };

formula :
| qformula     { $1 }
| formula Impl formula { Disj (Neg $1, $3) }
| formula Revimpl formula { Disj (Neg $3, $1) }
| formula Eqvt formula  { Eqiv ($1, $3) }
| formula And formula { Conj ($1, $3) }
| formula Or formula { Disj ($1, $3) }
| formula Neqvt formula { Neg (Eqiv ($1, $3)) }

qformula :
  Word { Atom ($1, []) }
| Word Openp ts { Atom ($1, $3) }
| fterm Eq fterm { Atom ("=", [$1; $3]) }
| fterm Neq fterm { Neg (Atom ("=", [$1; $3])) }
| Tilde qformula { Neg $2 }
| All qformula { list_forall (List.map var $1) $2 }
| Ex qformula { list_exists (List.map var $1) $2 }
| Openp formula Closep { $2 }

fterm :
  Word { if is_uppercase $1 then V (var $1) else A ($1, []) }
| Word Openp ts { A ($1, $3) }

ts :
  fterm Comma ts { $1 :: $3 }
| fterm Closep   { [$1] };

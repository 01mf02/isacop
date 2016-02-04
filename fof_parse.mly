%{
  open Cnf;;
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

%start fof_top fof_data
%type <(string * string * Cnf.form)> fof_top
%type <(Cnf.form * Cnf.form * Cnf.form list * Cnf.form list * Cnf.form * Cnf.form list * Cnf.form list)> fof_data
%%

fof_top :
  Word Openp Word Comma Word Comma formula Closep Dot { ($3, $5, $7) }
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
  Word { pred $1 [] }
| Word Openp ts { pred $1 $3 }
| fterm Eq fterm { Atom (eqn, [$1; $3]) }
| fterm Neq fterm { Neg (Atom (eqn, [$1; $3])) }
| Tilde qformula { Neg $2 }
| All qformula { list_forall $1 $2 }
| Ex qformula { list_exists $1 $2 }
| Openp formula Closep { $2 }

fterm :
  Word { if is_uppercase $1 then V (var $1) else const $1 [] }
| Word Openp ts { const $1 $3 }

ts :
  fterm Comma ts { $1 :: $3 }
| fterm Closep   { [$1] };

flist :
  formula Comma flist  { $1 :: $3 }
| formula Closep { [$1] }
| Closep { [] };

fof_data :
  formula Comma Openp formula Closep Comma Openp flist Comma Openp flist
          Comma Openp formula Closep Comma Openp flist Comma Openp flist
          Dot { ($1, $4, $8, $11, $14, $18, $21) }
| Eof { raise End_of_file };

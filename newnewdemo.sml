(* DATATYPE CATEGORIES AND FUNCTORS *) 

datatype ('o,'a) Cat = cat of ('a -> 'o) * ('a -> 'o) * ('o -> 'a) * (('a * 'a) -> 'a);

datatype ('oA,'aA, 'oB,'aB) Functor = ffunctor of ('oA, 'aA) Cat * ('oA -> 'oB) * ('aA -> 'aB) * ('oB,'aB) Cat;


(* LIST PROCESSING HELPERS *)


fun list_member(x,[]) = false |list_member(x,y::L) = x=y orelse list_member(x,L); 

fun list_remove(x,[]) = [] 
|list_remove(x,[y]) = if x=y then [] else [y] 
|list_remove(s,z::l) = if s=z then list_remove(s,l) else z::list_remove(s,l);

exception emptylist of unit;
val(emptylist_exception) = emptylist(());

fun is_sublist([],_) = true |is_sublist(e::L,[]) = false |is_sublist([e], L) = list_member(e,L) 
|is_sublist(e::L, u::M) = if (e=u) then is_sublist(L,M) else is_sublist(e::L,M); 
	
fun canonical_list(0) = [] |canonical_list(1) = [1] | canonical_list(n) = canonical_list(n-2) @ [n-1, n];

fun last(L) = hd(rev(L));

fun concat_list([]) = []
	|concat_list(x::L') = x @ concat_list(L');


(* THE CATEGORY FINSET*)


exception empty_set of unit; 
val emptysetexception = empty_set(());

abstype 'a Set = set of 'a list
	with val emptyset = set([]); 
	fun is_empty(set(s)) = length(s)=0; 
	fun singleton(x) = set([x]); 
	fun union(set(s),set(t)) = set(s@t);
	fun member(x,set(l)) = list_member(x,l); 
	fun remove(x,set(l)) = set(list_remove(x,l)); 
	fun weak_seteq(set(s),set(t),equality) = 
		length(s)=length(t) andalso (List.all(equality)) (ListPair.zip((s,t)));
	fun singleton_split(set(nil)) = raise emptysetexception 
	|singleton_split(set(x::s)) = (x, remove(x,set(s))); 
	fun split(s) = let val(x,s') = singleton_split(s) in (singleton(x),s') end 
	end;

fun seteq(A,B) = let val(x,A') = singleton_split(A) in 
			member(x,B) andalso seteq(A',remove(x,B)) end
		 handle emptysetexception => is_empty(A) andalso is_empty(B);

fun is_subset(A,B) = if is_empty(A) then true else let val(x,A')=singleton_split(A) in member(x,B) andalso is_subset(A',B) end;

fun imageset(f,S) = if is_empty(S) then emptyset else let val(x,S') = singleton_split(S) in union(singleton(f(x)),imageset(f,S')) end;

fun list_to_set([]) = emptyset |list_to_set(z::l) = union(singleton(z), list_to_set(l));

fun union_over_list([]) = emptyset |union_over_list(y::l) = union(y, union_over_list(l)); 

datatype 'a Set_Arrow = set_arrow of ('a Set) * ('a -> 'a) * ('a Set);


fun set_arroweq(set_arrow(A,f,B),set_arrow(A',f',B')) =  seteq(A,A') andalso seteq(B,B') 
	andalso let val(a,A'') = singleton_split(A) in f(a)=f'(a) 
		andalso set_arroweq(set_arrow(A'',f,B),set_arrow(remove(a,A'),f',B')) end;

fun fiber(x, set_arrow(A,f,B)) = if not(member(x,B)) then emptyset else 
	if is_empty(A) then emptyset else let val (y,A') = singleton_split(A) 
		in union(singleton(y), fiber(x, set_arrow(A',f,B))) end;

fun set_apply(f,U) = if is_empty(U) then emptyset else 
	let val (u,U') = singleton_split(U) in 
		union(singleton(f(u)), (set_apply(f,U'))) end;

fun Set_Source(set_arrow(a,_,_)) = a;

fun Set_Target(set_arrow(_,_,c)) = c;

fun Set_Identity(a) = set_arrow(a,fn x=>x,a);

exception non_composable of unit;
val non_composable_arrows = non_composable(());

fun Set_Composition(set_arrow(c,g,d),set_arrow(a,f,b)) = 
	if seteq(b,c) then set_arrow(a, fn x=>g(f(x)),d) else raise non_composable_arrows;

val FinSet = cat(Set_Source,Set_Target,Set_Identity,Set_Composition);

fun cartesian_prod(A,B) = if is_empty(A) then emptyset 
	else let val (a, A') = singleton_split A in 
		union(imageset(fn b => (a,b), B), cartesian_prod(A',B)) end;

fun prod_arrow(set_arrow(A,f,B), set_arrow(C,g,D)) = 
	set_arrow(cartesian_prod(A,C), (fn (x,y) => (f(x),g(y))), cartesian_prod(B,D));

val Diagonalproduct = ffunctor(FinSet, fn A => cartesian_prod(A,A), fn f => prod_arrow(f,f), FinSet);


(*SCHEMA CATEGORY*)


datatype Schema_Object = PERSON | INT | PRODUCT | ORDER;

datatype Schema_Arrow = ID of Schema_Object | NIL of Schema_Object * Schema_Object 
	|KNOWS |KEYVAL |NAME |PRODIDNAME |CREDITLIMITS |PRICE |I1 |I2
	|I1_KEYVAL |KEYVAL_NAME| I1_KEYVAL_NAME|I2_PRICE |I2_PRODIDNAME |KNOWS_NAME |KNOWS_CREDITLIMITS |KEYVAL_CREDITLIMITS |I1_KEYVAL_CREDITLIMITS;

fun Schema_Source(arrow) = case arrow of
	 ID(Z) => Z 
	|(NIL(X,Y)) => X
	|KNOWS => PERSON
	|KEYVAL => ORDER
	|NAME => PERSON
	|PRODIDNAME => PRODUCT
	|CREDITLIMITS => PERSON
	|PRICE => PRODUCT
	|I1 => INT
	|I2 => INT
	|I1_KEYVAL => INT
	|KEYVAL_NAME => ORDER 
	|KEYVAL_CREDITLIMITS => ORDER
	|I1_KEYVAL_CREDITLIMITS => INT	
	|I1_KEYVAL_NAME => INT
	|I2_PRICE => INT
	|I2_PRODIDNAME => INT
	|KNOWS_NAME => PERSON
	|KNOWS_CREDITLIMITS => PERSON;

fun Schema_Target(arrow) = case arrow of
	 ID(Z) => Z 
	|(NIL(X,Y)) => Y
	|KNOWS => PERSON
	|KEYVAL => PERSON
	|NAME => PERSON
	|PRODIDNAME => PRODUCT
	|CREDITLIMITS => INT
	|PRICE => INT
	|I1 => ORDER
	|I2 => PRODUCT
	|I1_KEYVAL => PERSON
	|I1_KEYVAL_NAME => PERSON
	|KEYVAL_NAME => PERSON
	|KEYVAL_CREDITLIMITS => INT
	|I1_KEYVAL_CREDITLIMITS => INT
	|I2_PRICE => INT
	|I2_PRODIDNAME => PRODUCT
	|KNOWS_NAME => PERSON
	|KNOWS_CREDITLIMITS => INT;

fun Schema_Identity(Z) = ID(Z);

fun Schema_Composition(arrow1, arrow2) = case (arrow1, arrow2) of
	(X, ID(_)) => X
	|(ID(_), Y) => Y 
	|(X, NIL(Z,Y)) => if Y = Schema_Source(X) then NIL(Z, Schema_Target(X)) 
		else raise non_composable_arrows
	|(NIL(Z,Y), X) => if Z = Schema_Target(X) then NIL(Schema_Source(X), Y) 
		else raise non_composable_arrows
	|(KNOWS,KNOWS) => KNOWS	
	|(NAME,KNOWS) => KNOWS_NAME
	|(CREDITLIMITS, KNOWS) => KNOWS_CREDITLIMITS 
	|(PRICE, I2) => I2_PRICE
	|(KEYVAL, I1) => I1_KEYVAL
	|(NAME, I1_KEYVAL) => I1_KEYVAL_NAME
	|(KEYVAL_NAME, I1) => I1_KEYVAL_NAME
	|(PRODIDNAME, I2) => I2_PRODIDNAME
	|(KNOWS, KEYVAL) => KEYVAL
	|(KNOWS, I1_KEYVAL) => I1_KEYVAL
	|(CREDITLIMITS, KEYVAL) => KEYVAL_CREDITLIMITS 
	|(CREDITLIMITS, I1_KEYVAL) => I1_KEYVAL_CREDITLIMITS
	|(KEYVAL_CREDITLIMITS, I1) => I1_KEYVAL_CREDITLIMITS
	|(A, B) => if Schema_Source(A) = Schema_Target(B) 
		then NIL(Schema_Target(A), Schema_Source(B)) 
			else raise non_composable_arrows;

val Schema = cat(Schema_Source, Schema_Target, Schema_Identity, Schema_Composition);


(* INSTANTIATION ALGORITHM *)

datatype Mult = 
	person of (int*string)*(int*string) 
	| intpair of int*int 
	| product of string*string*int 
	| order of string;

type InputData = 
	(int Set) *
	((int*int) Set) *
	(int -> (string*int)) *
	((string*((string*string*int) list)) list) *
	(string -> int);

fun NIL_element(x) = case x of
	INT => intpair((0,0))
	|PRODUCT => product((" "," ",0))
	|PERSON => person((0," "),(0," "))
	|ORDER => order(" ");

fun NIL_function(Y) = fn x => NIL_element(Y);

exception nosuchfunction of unit;
val nosuchfunction_exception = nosuchfunction(()); 

fun collect_orders1([]) = [] 
	|collect_orders1(E) = let val (s,L)::L' = E in order(s)::collect_orders1(L') end;

fun collect_orders2([]) = [] 
	|collect_orders2(E) = let val (s,L)::L' = E in (map(product)(L))::collect_orders2(L') end;

fun order_set(E) = list_to_set(order(" ")::collect_orders1(E));
fun product_set(E) = list_to_set(NIL_element(PRODUCT)::concat_list(collect_orders2(E)));

fun standard_list(x) = case x of 0 => [] | 1 => [1] | k => 1::map(fn x => x+1) (standard_list(k-1));
fun take_max(E) = ((map(length))(collect_orders2(E)));  

fun i_1(E) = fn intpair((0,_)) => NIL_element(ORDER)
		|intpair((k,0)) => if k>length(E) then NIL_element(ORDER) else
			 List.nth((collect_orders1(E), k-1))
		|intpair((_,j)) => NIL_element(ORDER);

fun i_2(E) = fn intpair((0,_)) => NIL_element(PRODUCT)
		|intpair((_,0)) => NIL_element(PRODUCT)
		|intpair((k,j)) => if k>length(E) orelse j>List.nth((take_max(E),k-1)) then
			NIL_element(PRODUCT) else List.nth(List.nth(collect_orders2(E), k-1), j-1);

fun name = fn 0 => " " |x => let val (s,i) = T(x) in s end;
fun credlim(T) = fn 0 => 0 |x => let val (s,i) = T(x) in i end;  

fun construct_persons(P,T) = if is_empty(P) then emptyset else let val(p,P') = singleton_split(P)
		in union((p, name(p)), construct_persons(P',T));

fun Name = fn person((x,m),(y,n)) => person((0,m),(0,n));
fun Credlim(T) = fn person((x,m),(y,n))) => intpair(0,credlim(T)(x));

fun Prod_id(product(a,b,c)) = product(a,b,0); 

fun Price(product(a,b,c)) = intpair((0,c));

fun keyval(s) = fn order(" ") => NIL_element(PERSON) 
	|order(o_no) => person((s(o_no), T(s(o_no))), (s(o_no), T(s(o_no))));

fun to_mult(constr) 
	= fn A => if is_empty(A) then emptyset else let val(a,A') = singleton_split(A) in 
		union(singleton(constr(a)), to_mult(constr)(A')) end;

fun person_set(P,T) = to_mult(person)
	((cartesian_prod(union(construct_persons(P,T), singleton((0, " "))),
	union(construct_personst(P,T), singleton((0, " ")))));

val INTSET = list_to_set(0::canonical_list(10000));

fun I_Obj((P,G,T,E,s)) = 
	fn PERSON => person_set(P,T)
	|INT => to_mult(intpair) (cartesian_prod(INTSET, INTSET))
	|ORDER => order_set(E)
	|PRODUCT => product_set(E) 

fun I_Arr((P,G,T,E,s)) =
	fn ID(X) => Set_Identity(I_Obj((P,G,T,E,s))(X))
	|NIL(Z,Y) => set_arrow(I_Obj((P,G,T,E,s))(Z), NIL_function(Y), I_Obj((P,G,T,E,s))(Y))
	|KNOWS => set_arrow(I_Obj((P,G,T,E,s))(PERSON), 
		fn person((x,y)) => if member((x,y),G) then person((x,y)) else person((0,0)),
		I_Obj((P,G,T,E,s))(PERSON))   
	|KEYVAL => set_arrow(I_Obj((P,G,T,E,s))(ORDER), keyval(s), I_Obj((P,G,T,E,s))(PERSON))
	|NAME => set_arrow(I_Obj((P,G,T,E,s))(PERSON), Name, I_Obj((P,G,T,E,s))(PERSON))
	|PRODIDNAME => set_arrow(I_Obj((P,G,T,E,s))(PRODUCT), Prod_id, I_Obj((P,G,T,E,s))(PRODUCT)) 
	|CREDITLIMITS => set_arrow(I_Obj((P,G,T,E,s))(PERSON), Credlim(T), I_Obj((P,G,T,E,s))(INT))
	|PRICE => set_arrow(I_Obj((P,G,T,E,s))(PRODUCT), Price, I_Obj((P,G,T,E,s))(INT))
	|I1 => set_arrow(I_Obj((P,G,T,E,s))(INT), i_1(E), I_Obj((P,G,T,E,s))(ORDER))
	|I2 => set_arrow(I_Obj((P,G,T,E,s))(INT), i_2(E), I_Obj((P,G,T,E,s))(PRODUCT))
	|I1_KEYVAL => Set_Composition(I_Arr((P,G,T,E,s))(KEYVAL), I_Arr((P,G,T,E,s))(I1))
	|KEYVAL_NAME => Set_Composition(I_Arr((P,G,T,E,s))(NAME), I_Arr((P,G,T,E,s))(KEYVAL))
	|KEYVAL_CREDITLIMITS => 
		Set_Composition(I_Arr((P,G,T,E,s))(CREDITLIMITS), I_Arr((P,G,T,E,s))(KEYVAL))
	|I1_KEYVAL_CREDITLIMITS => 
		Set_Composition(I_Arr((P,G,T,E,s))(CREDITLIMITS), I_Arr((P,G,T,E,s))(I1_KEYVAL))
	|I1_KEYVAL_NAME => Set_Composition(I_Arr((P,G,T,E,s))(NAME), I_Arr((P,G,T,E,s))(I1_KEYVAL))
	|I2_PRICE => Set_Composition(I_Arr((P,G,T,E,s))(PRICE), I_Arr((P,G,T,E,s))(I2)) 
	|I2_PRODIDNAME => Set_Composition(I_Arr((P,G,T,E,s))(PRODIDNAME), I_Arr((P,G,T,E,s))(I2)) 
	|KNOWS_NAME => Set_Composition(I_Arr((P,G,T,E,s))(NAME), I_Arr((P,G,T,E,s))(KNOWS)) 
	|KNOWS_CREDITLIMITS => 
		Set_Composition(I_Arr((P,G,T,E,s))(CREDITLIMITS), I_Arr((P,G,T,E,s))(KNOWS));

fun Inst((P,G,T,E,s)) = ffunctor(Schema, I_Obj((P,G,T,E,s)), I_Arr((P,G,T,E,s)), Mult Set);

  
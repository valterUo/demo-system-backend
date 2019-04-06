
(*First we define the data type of category with objects 'o, arrows 'a, the arguments being source, target, identity and composition, respectively. We also define functors.*) 

datatype ('o,'a) Cat = cat of ('a -> 'o) * ('a -> 'o) * ('o -> 'a) * (('a * 'a) -> 'a);

datatype ('oA,'aA, 'oB,'aB) Functor = ffunctor of ('oA, 'aA) Cat * ('oA -> 'oB) * ('aA -> 'aB) * ('oB,'aB) Cat;

(*Then some list processing functions.*)

fun append([],l) = l 
|append(x::h,k) = x::append(h,k);

fun list_member(x,[]) = false 
|list_member(y,[x]) = y=x 
|list_member(y,z::l) = if y=z then true else list_member(y,l);

fun list_remove(x,[]) = [] 
|list_remove(x,[y]) = if x=y then [] else [y] 
|list_remove(s,z::l) = if s=z then list_remove(s,l) else z::list_remove(s,l);

exception emptylist of unit;
val(emptylist_exception) = emptylist(());

fun head([]) = raise emptylist_exception | head([x]) = x | head(z::l) = z;
fun tail([]) = raise emptylist_exception | tail([x]) = [] | tail(z::l) = l;

fun list_size([]) = 0 |list_size(y::l) = 1 + list_size(l);

fun get(0,l) = raise emptylist_exception | get(1,l) = head(l) | get(k,y::l) = if k > list_size(y::l) then raise emptylist_exception else get(k-1,l);

fun list_apply(f,[]) = [] |list_apply(f,y::l) = f(y)::list_apply(f,l);

fun lists_concat([]) = [] |lists_concat([y]) = y |lists_concat(x::l) = 
	append(x, lists_concat(l));

fun canonical_list(0) = [] |canonical_list(1) = [1] |canonical_list(n) = append(canonical_list(n-1), [n]);

fun list_max([]) = 0 |list_max([x]) = x |list_max[x,y] = if x>y then x else y |list_max(h::l) = if h > list_max(l) then h else list_max(l);

(*We define the schema category Schema for the database.*)

datatype Schema_Object = PERSON | STR | INT | PRODUCT | ORDER;

datatype Schema_Edge = KNOWS | C_ID | PERSON_NAME | CREDIT_LIMITS | KEY_VAL 
	|INDEX_1 | INDEX_2 
	|ORDER_NO | PRODUCT_ID | PRODUCT_NAME | PRICE | ID of Schema_Object;  
	
fun Source_Target(KNOWS) = (PERSON, PERSON) 
	| Source_Target(C_ID) = (PERSON, INT) 
	| Source_Target(PERSON_NAME) = (PERSON, STR) 
	| Source_Target(CREDIT_LIMITS) = (PERSON, INT) 
	| Source_Target(KEY_VAL) = (INT, STR) 
	| Source_Target(INDEX_1) = (INT, ORDER) 
	| Source_Target(INDEX_2) = (INT, PRODUCT)
	| Source_Target(ORDER_NO) = (ORDER, STR)  
	| Source_Target(PRODUCT_ID) = (PRODUCT, STR) 
	| Source_Target(PRODUCT_NAME) = (PRODUCT, STR) 
	| Source_Target(PRICE) = (PRODUCT, INT)
	| Source_Target(ID(Z)) = (Z,Z); 

fun first(a,b) = a;
fun second(a,b) = b;

fun Source(E) = first(Source_Target(E));
fun Target(E) = second(Source_Target(E));  

exception non_composable of unit;
val(non_composable_arrows) = non_composable(());

fun Path_Source([]) = raise emptylist_exception | Path_Source([x]) = Source(x) | Path_Source(y::l) = Source(y);	
fun Path_Target([]) = raise emptylist_exception | Path_Target([x]) = Source(x) | Path_Target(y::l) = let val(z::k) = rev(l) in Target(z) end; 			
fun is_valid_path([]) = false | is_valid_path([x]) = true | is_valid_path(y::l) = Target(y) = Path_Source(l) andalso is_valid_path(l);

fun cancel_identities([]) = raise emptylist_exception 
	| cancel_identities([x]) = [x]	 
	| cancel_identities [x, ID(Z)] = [x]
	| cancel_identities(ID(Z)::l) = cancel_identities(l) 
	| cancel_identities(y::l) = y::cancel_identities(l);

fun cancel_knows([]) = raise emptylist_exception 
	| cancel_knows([x]) = [x] 
	| cancel_knows(y::l) = if y=KNOWS andalso head(l)=KNOWS 
		then cancel_knows(l) else y::cancel_knows(l);

fun Schema_Composition(l,m) = if is_valid_path(l) andalso is_valid_path(m) 
	andalso Path_Target(l) = Path_Source(m) then 
	cancel_knows(cancel_identities(append(l,m)))
	else raise non_composable_arrows; 

fun Schema_Identity(Z) = [ID(Z)];

val Schema = cat(Path_Source, Path_Target, Schema_Identity, Schema_Composition);

(*We have now defined the schema category Schema. We need now to define the category FinSet.*)

exception empty_set of unit; 
val emptysetexception = empty_set(());

abstype 'a Set = set of 'a list
	with val emptyset = set([]); 
	fun is_empty(set(s)) = length(s)=0; 
	fun singleton(x) = set([x]); 
	fun union(set(s),set(t)) = set(append(s,t));
	fun member(x,set(l)) = list_member(x,l); 
	fun remove(x,set(l)) = set(list_remove(x,l)); 
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

datatype 'a Set_Arrow = set_arrow of ('a Set) * ('a->'a) * ('a Set);

fun is_valid_set_arrow(set_arrow(A,f,B)) = is_subset(imageset(f,A),B);

fun set_arroweq(set_arrow(A,f,B),set_arrow(A',f',B')) = seteq(A,A') andalso seteq(B,B') andalso if is_empty(A) then true 
	else let val(a,A'') = singleton_split(A) in f(a)=f'(a) andalso set_arroweq(set_arrow(A'',f,B),set_arrow(remove(a,A'),f',B')) end;

fun Set_Source(set_arrow(a,_,_)) = a;

fun Set_Target(set_arrow(_,_,c)) = c;

fun Set_Identity(a) = set_arrow(a,fn x=>x,a);

exception non_composable of unit;
val non_composable_arrows = non_composable(());

fun Set_Composition(set_arrow(c,g,d),set_arrow(a,f,b)) = 
	if seteq(b,c) then set_arrow(a, fn x=>g(f(x)),d) else raise non_composable_arrows;

val FinSet = cat(Set_Source,Set_Target,Set_Identity,Set_Composition);

(*We have defined the category FinSet. We need binary products, so we define a binary product functor.*)

fun cartesian_prod(A,B) = if is_empty(A) then emptyset else let val (a, A') = singleton_split A in union(imageset(fn b => (a,b), B), cartesian_prod(A',B)) end;

fun prod_arrow(set_arrow(A,f,B), set_arrow(C,g,D)) = set_arrow(cartesian_prod(A,C), (fn (x,y) => (f(x),g(y))), cartesian_prod(B,D));

val Diagonalproduct = ffunctor(FinSet, fn A => cartesian_prod(A,A), fn f => prod_arrow(f,f), FinSet);

(*In order to handle instances in Finset, we need to fit many data types to one.*)

fun set_apply(f,U) = if is_empty(U) then emptyset else 
	let val (u,U') = singleton_split(U) in 
		union(singleton(f(u)), (set_apply(f,U'))) end;

datatype Mult = NIL | IINT of int | ISTR of string | INTPAIR of int * int 
	| STRPAIR of string * string | IPRODUCT of string * string * int;

fun knows(G) 
	= fn INTPAIR(x:int, y:int) => if member((x:int, y:int),G) then INTPAIR(x:int, y:int) 
		else INTPAIR(x:int, x:int);

fun c_id(INTPAIR(x:int, y:int)) = INTPAIR((x:int, y:int));

fun person_name(T)
	= fn INTPAIR(x:int, y:int) => STRPAIR(first(T(x)), first(T(y)));

fun credit_limits(T)
	= fn INTPAIR(x:int, y:int) => INTPAIR(second(T(x)), second(T(y)));

fun key_val(S,s)
	= fn INTPAIR(x:int, y:int) => 
		STRPAIR((if member(x,S) then s(x) else " "),(if member(y,S) then s(y) else " ")); 

fun order_no(ISTR(x)) = STRPAIR((x,x));
		  
fun index_1(E)
	= fn INTPAIR(0:int,_) => NIL |INTPAIR(k:int,0:int) => let val ([N])=E in 
		ISTR(first(get(k, N))) handle emptylist_exception => NIL end; 

fun index_2(E) = fn INTPAIR(k:int,l:int) => let val ([N])=E in 
	IPRODUCT(get (l, (second(get(k, N))))) end handle emptylist_exception => NIL;

fun product_id(IPRODUCT((a,_,_))) = STRPAIR(a,a);

fun product_name(IPRODUCT((_,b,_))) = STRPAIR(b,b);

fun price(IPRODUCT((_,_,c))) = INTPAIR(c,c);

(* Now we have all the functions so that they indeed are functions in Mult. We build then the sets.*)

fun person_set(P) = set_apply(INTPAIR, cartesian_prod(P,P));

fun order_set(E) = let val [N] = E in list_to_set(list_apply (ISTR, (list_apply (first, N)))) end;

fun product_set(E) = let val [N] = E in 
	list_to_set(list_apply(IPRODUCT, (lists_concat(list_apply(second, N))))) end; 

fun string_set(P,T,E,S,s) = union_over_list([imageset(key_val(S,s),set_apply(INTPAIR, (cartesian_prod(S,S)))), imageset (product_id, product_set(E)), 
imageset(product_name, product_set(E)),imageset(person_name(T), person_set(P)), imageset(order_no, order_set(E))]);

fun can (E) = let val [N] = E in 
	canonical_list(list_max(list_apply(list_size, (list_apply(second, N))))) end;

fun can'(E) = let val [N] = E in canonical_list(list_size(N)) end; 

fun indexset(E) = 
	set_apply(INTPAIR, cartesian_prod(list_to_set(can'(E)),list_to_set(can(E))));

fun int_set(P,T,E,S:int Set,s) = 
	union_over_list([set_apply(INTPAIR, (cartesian_prod(S,S))), indexset(E), imageset(c_id, person_set(P)), imageset(credit_limits(T), person_set(P)), imageset(price, product_set(E))]);

(*Finally we have everything ready and can define the instances.*)

fun ObjectFunct(P,G,T,E,S,s) = fn PERSON => person_set(P) 
	|STR => string_set(P,T,E,S,s) 
	|INT => int_set(P,T,E,S,s) 
	|PRODUCT => product_set(E) 
	|ORDER => order_set(E);

fun ArrowFunct(P,G,T,E,S,s) = fn [KNOWS] => set_arrow(person_set(P), knows(G), person_set(P))
  	|[C_ID] => set_arrow(person_set(P), c_id, int_set(P,T,E,S:int Set,s)) 
	|[PERSON_NAME] => set_arrow(person_set(P), person_name(T), string_set(P,T,E,S,s))
	|[CREDIT_LIMITS] => set_arrow(person_set(P), credit_limits(T), int_set(P,T,E,S:int Set,s))
	|[KEY_VAL] => set_arrow(int_set(P,T,E,S:int Set,s), key_val(S,s), string_set(P,T,E,S,s)) 
	|[INDEX_1] => set_arrow(int_set(P,T,E,S:int Set,s), index_1(E), order_set(E))  
	|[INDEX_2] => set_arrow(int_set(P,T,E,S:int Set,s), index_2(E), product_set(E))  
	|[ORDER_NO] => set_arrow(order_set(E), order_no, string_set(P,T,E,S,s))  
	|[PRODUCT_ID] => set_arrow(product_set(E), product_id, string_set(P,T,E,S,s))  
	|[PRODUCT_NAME] => set_arrow(product_set(E), product_name, string_set(P,T,E,S,s))  
	|[PRICE] => set_arrow(product_set(E), price, int_set(P,T,E,S:int Set,s)) 
	|[ID(STR)] => Set_Identity(ObjectFunct(P,G,T,E,S,s)(STR))
	|[ID(INT)] => Set_Identity(ObjectFunct(P,G,T,E,S,s)(INT))
	|[ID(PERSON)] => Set_Identity(ObjectFunct(P,G,T,E,S,s)(PERSON))
	|[ID(PRODUCT)] => Set_Identity(ObjectFunct(P,G,T,E,S,s)(PRODUCT))
	|[ID(ORDER)] => Set_Identity(ObjectFunct(P,G,T,E,S,s)(ORDER))
	|L => let val l::L' = L in Set_Composition(ArrowFunct(P,G,T,E,S,s)(L'),ArrowFunct(P,G,T,E,S,s)([l])) end;
	
fun Instance_Maker(P,G,T,E,S,s) = 
	ffunctor(Schema, ObjectFunct(P,G,T,E,S,s), ArrowFunct(P,G,T,E,S,s), FinSet);

(*We have defined the instance depending on P,G,T,E,S,s in general case. Then the example.*)

val P' = list_to_set([1,2,3]);
val G' = list_to_set([(2,1), (1,3)]);
val T' = fn 1 => ("Mary", 5000:int) |2 => ("John", 3000:int) |3 => ("William", 2000:int);
val E' = [[("0c6df508",[("2724f","Toy",66), ("3424g", "Book", 40)])]];
val S' = list_to_set([1,2]);
val s' = fn 1 => "34e5e79" | 2 => "0c6df508";

val Instance = Instance_Maker(P',G',T',E',S',s');

(* Now we can begin the real work, namely the queries. In its simplest form, it is like this.*)






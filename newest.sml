(* 0:  CATEGORY THEORY GENERAL FORMULAS *) 

datatype ('o,'a) Cat = cat of ('a -> 'o) * ('a -> 'o) * ('o -> 'a) * (('a * 'a) -> 'a);

datatype ('oA,'aA, 'oB,'aB) Functor = ffunctor of ('oA, 'aA) Cat * ('oA -> 'oB) * ('aA -> 'aB) * ('oB,'aB) Cat;

datatype ('oA,'aA, 'oB,'aB) Nat_Transform 
	= nat_transform of ('oA,'aA, 'oB,'aB) Functor * ('oA -> 'aB) * ('oA,'aA, 'oB,'aB) Functor


(* 0,01:  EXTREMELY GENERAL STUFF  *)

fun first(a,b) = a;
fun second(a,b) = b;
fun diagonal(a) = (a,a);


(* 1:  LIST PROCESSING HELPERS  *)

fun list_member(x,[]) = false |list_member(x,y::L) = x=y orelse list_member(x,L); 

fun list_remove(x,[]) = [] 
|list_remove(x,[y]) = if x=y then [] else [y] 
|list_remove(s,z::l) = if s=z then list_remove(s,l) else z::list_remove(s,l);

exception emptylist of unit;
val(emptylist_exception) = emptylist(());

fun is_sublist([],_) = true |is_sublist(e::L,[]) = false |is_sublist([e], L) = list_member(e,L) 
|is_sublist(e::L, u::M) = if (e=u) then is_sublist(L,M) else is_sublist(e::L,M); 
	
fun canonical_list(0) = [0] | canonical_list(n) = rev(n::canonical_list(n-1));

fun enumerated_list([],_) = [] |enumerated_list(x::L,k) = (k,x)::enumerated_list(L,k+1);

fun enum_list(L) = enumerated_list(L,0);

fun last(L) = hd(rev(L));

fun concat_list([]) = []
	|concat_list(x::L') = x @ concat_list(L');

fun listProd xs ys = List.concat(List.map(fn x => List.map(fn y => (x,y)) ys) xs);

fun list_size([]) = 0 |list_size(x::X') = 1+list_size(X');

fun sumlistrec[] = 0 |sumlistrec((j::L):int list) = j+sumlistrec(L);


(*  2: THE CATEGORY FINSET  *)

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

fun cardinality(A) = let val (a,A') = singleton_split(A) in 1 + cardinality(A') handle emptysetexception => 0 end;

datatype 'a Set_Arrow = set_arrow of ('a Set) * ('a -> 'a) * ('a Set);

fun set_arroweq(set_arrow(A,f,B),set_arrow(A',f',B')) =  seteq(A,A') andalso seteq(B,B') 
	andalso let val(a,A'') = singleton_split(A) in f(a)=f'(a) 
		andalso set_arroweq(set_arrow(A'',f,B),set_arrow(remove(a,A'),f',B')) end;

fun set_apply(f,U) = if is_empty(U) then emptyset else 
	let val (u,U') = singleton_split(U) in 
		union(singleton(f(u)), (set_apply(f,U'))) end;

fun Set_Extract_Function(set_arrow(_,f,_)) = f;

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


(* 3: SCHEMA CATEGORY   *)

datatype Schema_Object = PERSON | INT | PRODUCT | ORDER;

fun schemaobj_to_string(X) = case X of 
	PERSON => "PERSON"
	|INT => "INT"
	|PRODUCT => "PRODUCT"
	|ORDER => "ORDER";

datatype Schema_Arrow = ID of Schema_Object | NIL of Schema_Object * Schema_Object 
	|KNOWS |KEYVAL |CREDITLIMITS |PRICE |I1 |I2
	|I1_KEYVAL |I2_PRICE |KNOWS_CREDITLIMITS |KEYVAL_CREDITLIMITS |I1_KEYVAL_CREDITLIMITS;

fun schemaarr_to_string(X) = case X of
	KNOWS => "KNOWS"
	|KEYVAL => "KEYVAL"
	|CREDITLIMITS => "CREDITLIMITS"
	|PRICE => "PRICE" 
	|I1 => "I1"
	|I2 => "I2"
	|I1_KEYVAL => "I1_KEYVAL"
 	|I2_PRICE => "I2_PRICE" 
	|KNOWS_CREDITLIMITS => "KNOWS_CREDITLIMITS"
	|KEYVAL_CREDITLIMITS => "KEYVAL_CREDITLIMITS"
	|I1_KEYVAL_CREDITLIMITS => "I1_KEYVAL_CREDITLIMITS";

fun Schema_Source(arrow) = case arrow of
	 ID(Z) => Z 
	|NIL(X,Y) => X
	|KNOWS => PERSON
	|KEYVAL => ORDER
	|CREDITLIMITS => PERSON
	|PRICE => PRODUCT
	|I1 => INT
	|I2 => INT
	|I1_KEYVAL => INT
	|KEYVAL_CREDITLIMITS => ORDER
	|I1_KEYVAL_CREDITLIMITS => INT	
	|I2_PRICE => INT
	|KNOWS_CREDITLIMITS => PERSON;

fun Schema_Target(arrow) = case arrow of
	 ID(Z) => Z 
	|NIL(X,Y) => Y
	|KNOWS => PERSON
	|KEYVAL => PERSON
	|CREDITLIMITS => INT
	|PRICE => INT
	|I1 => ORDER
	|I2 => PRODUCT
	|I1_KEYVAL => PERSON
	|KEYVAL_CREDITLIMITS => INT
	|I1_KEYVAL_CREDITLIMITS => INT
	|I2_PRICE => INT
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
	|(CREDITLIMITS, KNOWS) => KNOWS_CREDITLIMITS 
	|(PRICE, I2) => I2_PRICE
	|(KEYVAL, I1) => I1_KEYVAL
	|(KNOWS, KEYVAL) => KEYVAL
	|(KNOWS, I1_KEYVAL) => I1_KEYVAL
	|(CREDITLIMITS, KEYVAL) => KEYVAL_CREDITLIMITS 
	|(CREDITLIMITS, I1_KEYVAL) => I1_KEYVAL_CREDITLIMITS
	|(KEYVAL_CREDITLIMITS, I1) => I1_KEYVAL_CREDITLIMITS
	|(A, B) => if Schema_Source(A) = Schema_Target(B) 
		then NIL(Schema_Target(A), Schema_Source(B)) 
			else raise non_composable_arrows;

val Schema = cat(Schema_Source, Schema_Target, Schema_Identity, Schema_Composition);


(*  4. THE DATATYPE MULT   *)

datatype Product = product of string * string * int;
val NIL_product = product(" "," ",0);
fun product_to_string(product(a,b,c)) = "product(" ^ a ^ "," ^ b^ "," ^ Int.toString(c) ^ ")";

datatype Intpair = DOUBLE_ZERO | right of int | left of int | leftright of (int * int); 
fun intpair_to_string(DOUBLE_ZERO) = "DOUBLE_ZERO"
	|intpair_to_string(right(x)) = "right(" ^ Int.toString(x) ^ ")"
	|intpair_to_string(left(x)) = "left(" ^ Int.toString(x) ^ ")"
	|intpair_to_string(leftright(x:int,y:int)) = 
		"leftright(" ^ Int.toString(x) ^ "," ^ Int.toString(y)  ^ ")";

datatype Order = order_no of string;
val NIL_order = order_no(" ");
fun order_to_string(order_no(s)) = "order_no " ^ s;

datatype Person = NIL_person | person of (int*string)*(int*string);

fun Person_Name(NIL_person) = " " |Person_Name(person((a,b),(c,d))) = b;
fun Person_ID(NIL_person) = ~1 |Person_ID(person((a,b),(c,d))) = a; 

fun person_to_string(NIL_person) = "NIL_person"
	|person_to_string(person((a:int,b),(c:int,d))) = 
		"person(" ^ Int.toString(a) ^ "," ^ b ^"),(" ^ Int.toString(c) ^ "," ^ d ^ "))"

datatype Mult = multP of Person | multI of Intpair | multR of Product | multO of Order;

fun NIL_elem(PERSON) = multP(NIL_person) 
	|NIL_elem(INT) = multI(DOUBLE_ZERO) 
	|NIL_elem(ORDER) = multO(NIL_order)
	|NIL_elem(PRODUCT) = multR(NIL_product);

fun mult_to_string(multP(p)) = "mult" ^ person_to_string(p)
	|mult_to_string(multI(x)) = "mult" ^ intpair_to_string(x)
	|mult_to_string(multR(y)) = "mult" ^ product_to_string(y)
	|mult_to_string(multO(z)) = "mult" ^ order_to_string(z)	


(*   5: INSTANTIATION *)

datatype Customer = customer of (int*string);

fun Customer_List(input) = let val(T:(string*int) list,Gr:(int*int) list,Er:(string * (string*string*int)list) list,mr:(string -> int)) = 
	input in enum_list(map(first)(T)) end;

fun Customer_Name(input) = fn j => second(List.nth(Customer_List(input),j));
		 
fun Customer_Number(input) = let val(T:(string*int) list,Gr:(int*int) list,Er:(string * (string*string*int)list) list,mr:(string -> int)) = 
	input in list_size(T) end;

fun Raw_Person_List(input) = let val L = Customer_List(input) in (listProd(L))(L) end;

fun Person_List(input) = (map(person))(Raw_Person_List(input));

fun Person_Set(input) = list_to_set(NIL_person::Person_List(input));

fun Order_List(input) = let val(T:(string*int) list,Gr:(int * int) list,E:((string * (string*string*int)list) list),mr:(string -> int)) = input in
	(map(order_no))((map(first))(E)) end;

fun Raw_Product_List(input) = let val(T:(string*int) list,Gr:((int * int) list),E:((string * (string*string*int)list) list),mr:(string -> int)) = input in List.concat(((map(second))(E))) end;

fun Product_List(input) = (map(product))(Raw_Product_List(input));

exception nosuch of unit;
val nosuch_person = nosuch(()); 

fun creditlimits(i) = let val((T:(string*int) list,Gr:(int * int) list,Er:(string * (string*string*int)list) list,mr:(string -> int))) = i in
		fn person((k,n),(j,m)) => if k < length(T) andalso j < length(T) then
			right(second(List.nth(T,k))+second(List.nth(T,j))) else raise nosuch_person 
		|NIL_person => DOUBLE_ZERO end;

fun mult_creditlimits(i) = fn multP(p) => multI(creditlimits(i)(p));

fun raw_price((product(_,_,c))) = right(c);
fun raw_order_id((product(a,_,_))) = a;
fun raw_order_name(multR(product(_,b,_))) = b;
fun price(multR(product(_,_,c))) = multI(right(c));
fun price_toint(multR(product(_,_,c))) = c;
fun order_id(multR(product(a,_,_))) = a;
fun order_name(multR(product(_,b,_))) = b;

fun indexation_1(i) = let val((T:(string*int) list,Gr:(int * int) list,E:(string * (string*string*int)list) list,mr:(string -> int))) = i
	in fn k => if k > length(E)-1 then NIL_order 
		   else order_no(first(List.nth(E,k))) end;

fun indexation_2(i) = let val((T:(string*int) list,Gr:(int * int) list,E:(string * (string*string*int)list) list,mr:(string -> int))) = i 
	in fn (k,j) => if k > length(E)-1 then NIL_product	
		  else if j > length(second(List.nth(E,k)))-1 then NIL_product
			else product(List.nth(second(List.nth(E,k)), j)) end;

fun i1(i) = fn multI(DOUBLE_ZERO) => NIL_elem(ORDER)
		|multI(right(x)) => NIL_elem(ORDER)
		|multI(leftright(y,t)) => NIL_elem(ORDER)
		|multI(left(z)) => multO(indexation_1(i)(z));

fun i2(i) = fn multI(DOUBLE_ZERO) => NIL_elem(PRODUCT) 
		|multI(right(x)) => NIL_elem(PRODUCT)
		|multI(leftright(y,t)) => multR(indexation_2(i)(y,t))
		|multI(left(z)) => NIL_elem(PRODUCT);

fun max(i) = if list_size(Order_List(i))> 0 then list_size(Order_List(i))-1 else 0;
fun indexlist1(i) = canonical_list(max(i));
fun indexset1(i) = list_to_set(map(multI o left)((indexlist1(i))));

fun product_sizes(i) = let val(_,_,E,_) = i in 
	fn k => if k<=max(i) then list_size(second(List.nth(E,k)))-1 else 0 end;

fun llist(k:int,0:int) = [(k,0)] |llist(k:int,j:int) = (k,j)::llist(k,j-1);
fun append(i) = fn 0:int => llist(0,(product_sizes(i)(0))) |r:int => llist(r,(product_sizes(i)(r))) @ append(i)(r-1);
fun productlist(i) = append(i)(max(i));
fun indexset2(i) = (list_to_set(map(multI o leftright)(productlist(i)))); 


fun Instance_Objects(i) = 
	fn PERSON => 
		union(singleton(multP(NIL_person)), list_to_set(map(multP)((Person_List(i)))))
	|ORDER => 
		union(singleton(multO(NIL_order)), list_to_set(map(multO)((Order_List(i)))))
	|PRODUCT => 
		union(singleton(multR(NIL_product)), list_to_set(map(multR)((Product_List(i)))))
	|INT => union_over_list([singleton(multI(DOUBLE_ZERO)), 
		 list_to_set(map(multI o creditlimits(i))((Person_List(i)))),
		 imageset(price, Instance_Objects(i)(PRODUCT)),
	 	indexset1(i), indexset2(i), singleton(multI(leftright((0:int,0:int))))]);
		   	
fun mult_set_to_string(A) = let val (a,A') =singleton_split(A) in 
	mult_to_string(a) ^"\n"^ mult_set_to_string(A') 
		handle emptysetexception => " " end;

fun knows(i) = let val((T:(string*int)list, G:(int*int)list, Er:(string * (string*string*int)list) list,mr:(string -> int))) = i in
		fn person((k,n),(j,m)) => if k < length(T) andalso j < length(T) then
			(if list_member((k,j),G) orelse k=j then person((k,n),(j,m)) 
						else NIL_person)
			else raise nosuch_person		
		|NIL_person => NIL_person end;

fun mult_knows(i) = fn multP(p) => multP(knows(i)(p));



fun keyval(i) = let val((T:(string*int) list,Gr:(int * int) list,Er:(string * (string*string*int)list) list,s:string -> int)) = i in
	fn (order_no(ono)) => if s(ono) < length(T) then 
		person(diagonal((s(ono),List.nth(((map(first))(T)), s(ono)))))
			else raise nosuch_person end;

fun mult_keyval(i) = fn multO(x) => multP(keyval(i)(x));

fun Instance_Func_Mult(i:(string*int)list * (int * int) list * 
(string * (string*string*int)list) list * (string -> int)) =
	 fn KNOWS => mult_knows(i)
	 |CREDITLIMITS => mult_creditlimits(i)
	 |KEYVAL => mult_keyval(i)			
	 |I1 => i1(i)	 
	 |I2 => i2(i)
	 |PRICE => price
	 |KNOWS_CREDITLIMITS => mult_creditlimits(i) o mult_knows(i)
	 |KEYVAL_CREDITLIMITS => mult_creditlimits(i) o mult_keyval(i)
	 |I1_KEYVAL_CREDITLIMITS => mult_creditlimits(i) o mult_keyval(i) o i1(i) 
	 |I2_PRICE => price o i2(i)
	 |I1_KEYVAL => mult_keyval(i) o i1(i)
	 |ID(Z) => let val set_arrow(_,h,_) = Set_Identity(Instance_Objects(i)(Z)) in h end
	 |NIL(X,Y) => fn _ => NIL_elem(Y); 


fun InstanceSource(i) = fn A:Schema_Arrow => ((Instance_Objects(i))(Schema_Source(A)));
fun InstanceTarget(i) = fn A:Schema_Arrow => ((Instance_Objects(i))(Schema_Target(A)));

fun Instance_SetArrows(i) = fn (A:Schema_Arrow) => 
	set_arrow(InstanceSource(i) A ,Instance_Func_Mult(i) A , InstanceTarget(i) A );

fun mult_set_arrow_to_string(set_arrow(A,f,B)) = 
	"mult A,B" ^ ":" ^ let val (a,A') = singleton_split(A) in mult_to_string(a) ^ "->" ^ 			 mult_to_string(f(a)) ^ " " ^"\n"^  mult_set_arrow_to_string(set_arrow(A',f,B)) 
		handle emptysetexception => " " end;

val MultSet = FinSet: (Mult Set, Mult Set_Arrow) Cat;

fun Inst(i:(string*int)list * (int * int) list * 
(string * (string*string*int)list) list * (string -> int)) 
= ffunctor(Schema, Instance_Objects(i), Instance_SetArrows(i), MultSet);  

	 	
(*  6:  TESTS *)

fun print_schemaobj(C) = print(schemaobj_to_string(C));
fun print_schemaarr(A) = print(schemaarr_to_string(A));
fun print_multset(S) = print(mult_set_to_string(S));
fun print_mult_set_arrow(A) = print(mult_set_arrow_to_string(A));
fun T_list_to_string([]) = " " 
	|T_list_to_string((x,i)::L) =  
		"("^ x ^ "," ^ Int.toString(i) ^ "),(" ^"\n"^  T_list_to_string(L);
fun print_T(L) = print(T_list_to_string(L)); 
fun G_list_to_string([]) = " " 
	|G_list_to_string((i:int,j:int)::L) = 
		"(" ^ Int.toString(i) ^ "," ^ Int.toString(j) ^ ")," ^"\n"^  G_list_to_string(L);
fun print_G(L) = print(G_list_to_string(L));
fun rawproduct_list_to_string([]) = " " 
	|rawproduct_list_to_string((a,b,c:int)::L) = 
		"("^a ^ ","^ b ^"," ^ Int.toString(c)^ ")," ^"\n"^  rawproduct_list_to_string(L);
fun E_list_to_string([]) = " "
	|E_list_to_string((s,L)::W) = 
		"order_no:" ^ s ^"\n"^  rawproduct_list_to_string(L) ^"\n"^  E_list_to_string(W);
fun print_E(L) = print(E_list_to_string(L)); 
fun order_nos_to_string([]) = " " 
	|order_nos_to_string ((s,L)::W) = 
		"order_no:" ^ s ^"\n"^ order_nos_to_string(W);
fun keyval_to_string([],s) = " " 
	|keyval_to_string ((x,L)::W,s) = 
		"order_no:" ^ x ^ "->" ^ Int.toString(s(x):int) ^"\n"^ keyval_to_string(W,s);
fun print_keyval(s,E) = print(keyval_to_string(s,E));

val T'' = [("Mary", 5000:int),("John", 2000:int), ("William", 3000:int), ("Daddy", 200:int), 		("William", 30:int), ("Erica", 8000:int), ("Mill", 0:int), ("Bob", 9999:int)];
val G'' = [(1,6), (3,6), (6,3), (3,1), (1,2), (0,5), (4,2), (4,5)];
val E'' = [("34e5e79", [("2343f", "Toy", 66:int), ("3424g", "Book", 40:int)]),
	   ("0cbdf508",[("2543f", "Guitar", 666:int), ("1234r", "Nothing", 1:int)]), 
	   ("4dwtfuu", [("2343f", "Toy", 66:int)]),
	   ("3qqqeq9", [("2343f", "Toy", 66:int), ("3424g", "Book", 40:int), 
			("3424g", "Book", 40:int), ("3424g", "Book", 40:int), 
			("2543f", "Guitar", 666:int)]),
	   ("77idy65", [("5467y", "Pen", 2:int), ("5698r", "Car", 9999:int)]),
	   ("ery63rg", [("7890u", "Cup", 24:int), ("5467y", "Pen", 2:int), ("3424g", "Book", 40:int),
			("2543f", "Guitar", 666:int), ("896h", "Jewelry", 5000:int), 
			("2343f", "Toy", 66:int)])]; 	
val sq' =      fn "34e5e79" => 1:int 
	 	|"0cbdf508" => 2:int 
		| "4dwtfuu" => 1:int
		|"3qqqeq9" => 0:int
		|"77idy65" => 3:int

		|"ery63rg" => 5:int;

val TESTINPUT = (T'', G'', E'', sq');
val TESTINST = Inst(T'',G'',E'',sq');
val ffunctor(_,io,_,_) = TESTINST;
val ffunctor(_,_,ia,_) = TESTINST;

fun io_to_string(X) = schemaobj_to_string(X) ^ ":" ^ mult_set_to_string(io(X))^ "\n";
fun ia_to_string(A) = schemaarr_to_string(A) ^ ":" ^ mult_set_arrow_to_string(ia(A))^"\n";


(*   7: SUBFUNCTORS *)

datatype SubFunctor = subfunctor of 
	(Schema_Object, Schema_Arrow, Mult Set, Mult Set_Arrow) Nat_Transform;

val SO_LIST = [PERSON, ORDER, PRODUCT, INT];
val SA_LIST = [KNOWS, CREDITLIMITS, I1, I2, KEYVAL, PRICE];

fun are_subsets(ffunctor(_, I'O, I'A, _), ffunctor(_, IO, IA, _)) 
	= ((List.all(fn X:Schema_Object => is_subset(I'O(X),IO(X))))(SO_LIST));

fun is_an_inclusion(set_arrow(A,f,B)) = let val (a, A') = singleton_split(A) in
	(f(a) = a) andalso is_an_inclusion(set_arrow(A',f,B)) handle emptysetexception => true end;

fun components_are_inclusions(subfunctor(nat_transform(I', comps, I))) 
	= ((List.all(fn X:Schema_Object => is_an_inclusion(comps(X))))(SO_LIST));

fun commutes ((subfunctor(nat_transform
	(ffunctor(_, I'O, I'A, _), comps, ffunctor(_, IO, IA, _)))),f:Schema_Arrow) 
		= let val (X,Y) = (Schema_Source(f),Schema_Target(f)) in set_arroweq(Set_Composition(comps(Y),I'A(f)), Set_Composition(IA(f), comps(X))) end;
	
fun commutes_for_all(subfunctor(nat_transform(I', comps, I))) = 
	((List.all(fn f:Schema_Arrow => commutes((subfunctor(nat_transform (I', comps, I))),f)))
	(SA_LIST));
   
fun is_real_subfunctor(S) = if components_are_inclusions(S) then commutes_for_all(S) else false;

fun REPR_OBJ(i:(string*int) list * (int*int) list * (string * (string*string*int)list) list *(string -> int)) = 
	fn (PERSON, PERSON) => (Instance_Objects(i))(PERSON) 
	|(PERSON, INT) => imageset((mult_creditlimits(i)), (Instance_Objects(i))(PERSON))
	|(PERSON, PRODUCT) => singleton(NIL_elem(PRODUCT))
	|(PERSON, ORDER) =>  singleton(NIL_elem(ORDER))
	|(ORDER, PERSON) => imageset((mult_keyval(i)), (Instance_Objects(i))(ORDER))
	|(ORDER, INT) => imageset((mult_creditlimits(i) o mult_keyval(i)), 
		(Instance_Objects(i))(ORDER))
	|(ORDER, PRODUCT) => singleton(NIL_elem(PRODUCT))
	|(ORDER, ORDER) => (Instance_Objects(i))(ORDER)
	|(INT,PERSON) => 
		imageset((mult_keyval(i) o i1(i)), (Instance_Objects(i))(INT)) 
	|(INT,INT) => (Instance_Objects(i))(INT) 
	|(INT,PRODUCT) => 
		imageset(i2(i), (Instance_Objects(i))(INT)) 
	|(INT,ORDER) => 
		imageset(i1(i), (Instance_Objects(i))(INT)) 
	|(PRODUCT,PERSON) => singleton(NIL_elem(PERSON))
	|(PRODUCT,INT) => imageset(price, (Instance_Objects(i))(PRODUCT))
	|(PRODUCT,PRODUCT) => (Instance_Objects(i))(PRODUCT)
	|(PRODUCT,ORDER) => singleton(NIL_elem(ORDER));	 

fun REPRR_OBJ(i,X:Schema_Object) = fn Y:Schema_Object => REPR_OBJ(i)(X,Y);

fun REPR_ARR(i,X:Schema_Object) =     		
	fn f: Schema_Arrow => set_arrow(REPR_OBJ(i)(X, Schema_Source(f)), 
	fn x => (Instance_Func_Mult(i)(f))(x), 
	REPR_OBJ(i)(X,Schema_Target(f)));

fun REPR(i, X:Schema_Object) = ffunctor(Schema, REPRR_OBJ(i,X), REPR_ARR(i,X), MultSet);

fun sub(T:(string*int) list,G:(int*int) list,E:(string * (string*string*int)list) list,s:(string -> int),X:Schema_Object) = let
	val I = ffunctor(Schema, Instance_Objects(T,G,E,s), Instance_SetArrows(T,G,E,s), MultSet) in  
	subfunctor(nat_transform
	(REPR((T,G,E,s),X), 
	fn Y => set_arrow(REPRR_OBJ((T,G,E,s),X)(Y), fn x => x, Instance_Objects(T,G,E,s)(Y)), I)) end;


(*   8 : TotalPrice *)

fun cancel_right(right(x:int)) = x;

fun cancel_multI(multI(right(z))) = right(z) |cancel_multI(multI(left(x))) = left(x)
	|cancel_multI(multI(leftright(a,b))) = leftright(a,b)
	|cancel_multI(multI(DOUBLE_ZERO)) = DOUBLE_ZERO;

fun cancel_multP(multP(person((a,b),(c,d)))) = person((a,b),(c,d)) 
	|cancel_multP(multP(NIL_person)) = NIL_person;

fun cancel_multR(multR(product(a,b,c))) = product(a,b,c);
	
fun sum_over_int(0, f:int -> int) = f(0) | sum_over_int(n, f:int->int) = f(n)+sum_over_int(n-1,f);

fun TotalPrice(i:((string*int) list * (int*int) list * (string * (string*string*int)list) list *(string -> int))) = fn k:int => if 0 <=k andalso k<=max(i) then 
	sum_over_int((product_sizes(i))(k), 
fn j:int => cancel_right(cancel_multI((Instance_Func_Mult(i))(I2_PRICE)(multI(leftright(k,j)))))) 
				else 0; 

fun inverse(i)(p) = fn multO(order_no(onostring)) => 
			if 0<=p andalso p <= max(i) then
				if order_no(onostring) = hd(List.drop(Order_List(i),p)) then p 
				else (inverse(i)(p+1))((multO(order_no(onostring))))
			else ~1;

fun Inverse(i)((multO(order_no(onostring)))) = if onostring = " " then 0 else (inverse(i)(0))(multO(order_no(onostring)));
		
fun Total_Price(i) = TotalPrice(i) o Inverse(i);

fun new_INT_Set(i) = union(Instance_Objects(i)(INT), imageset(multI o right o Total_Price(i), remove(NIL_elem(ORDER),Instance_Objects(i)(ORDER)))); 

fun INSTANCE_Objects(i) = fn PERSON => Instance_Objects(i)(PERSON)
			|ORDER => Instance_Objects(i)(ORDER)
			|PRODUCT => Instance_Objects(i)(PRODUCT)
			|INT => new_INT_Set(i);

fun INSTANCESource(i) = fn A:Schema_Arrow => ((INSTANCE_Objects(i))(Schema_Source(A)));
fun INSTANCETarget(i) = fn A:Schema_Arrow => ((INSTANCE_Objects(i))(Schema_Target(A)));

fun INSTANCE_SetArrows(i) = fn (A:Schema_Arrow) => 
	set_arrow(INSTANCESource(i) A ,Instance_Func_Mult(i) A , INSTANCETarget(i) A);

fun INSTANCE(i) = ffunctor(Schema, INSTANCE_Objects(i), INSTANCE_SetArrows(i), MultSet); 


(* 9:  The view J(i) *)

datatype J_OBJ = c |s |I |O |p;

datatype J_ARR = Ordered |C_Name |C_Name_Ordered |C_ID |Cred_lim |P_ID |P_Name |T_Price |P_Price
		|Or_no |ID of J_OBJ;

datatype J_REL = REL_KNOWS |REL_CPo |REL_CPp |REL_CONTAINS;

fun J_Source(x) = case x of Ordered => O |C_Name => c |C_Name_Ordered => O |C_ID => c |Cred_lim => c 	|P_ID => p |P_Name => p |T_Price => O |P_Price => p |Or_no => O |ID(x) => x;

fun J_Target(x) = case x of Ordered => c |C_Name => s |C_Name_Ordered => s |C_ID => I |Cred_lim => I |P_ID => s |P_Name => s |T_Price => I |P_Price => I|Or_no => s |ID(x) => x;

fun J_Identity(x) = ID(x);

fun J_Composition(g,f) = case (g,f) of 
	(ID(x),f) => if J_Target(f) = x then f else raise non_composable_arrows
	|(g,ID(y)) => if J_Source(g) = y then g else raise non_composable_arrows
	|(C_Name, Ordered) => C_Name_Ordered
	|(h,k) => raise non_composable_arrows;

val Schema_J = cat(J_Source, J_Target, J_Identity, J_Composition);

datatype Just_for_J = string | int | m of Mult Set;

fun cancel_m(m(x)) = x;
val doubles_to_mult = multP o person o (fn x => (x,x));
fun cancel_multO_order(multO(order_no(onostring))) = onostring;
val customername = Person_Name o cancel_multP;
val customerid = Person_ID o cancel_multP;
val doublecancel = cancel_right o cancel_multI;
val idc = fn multP(z) => multP(z);
    val idp = fn multR(z) => multR(z);
    val ido = fn multO(z) => multO(z);
    val ids = fn z:string => z:string;
    val idi = fn k:int => k:int;    

fun JO(i:(string*int) list * (int*int) list * (string * (string*string*int)list) list *(string -> int)) = fn 
	    c => m(list_to_set(map(doubles_to_mult)((Customer_List(i)))))
	    |s => string
	    |I => int
	    |O => m(INSTANCE_Objects(i)(ORDER))	
	    |p => m(INSTANCE_Objects(i)(PRODUCT));

fun indirect_Source(i) = JO(i) o J_Source;
fun indirect_Target(i) = JO(i) o J_Target;

datatype Just_for_J_again = M of Mult Set * (Mult -> Mult) | MS of Mult Set * (Mult -> string) | MI of Mult Set * (Mult -> int) |S of string -> string |II of int -> int;

fun identity_J(string) = S(ids) |identity_J(int) = II(idi) |identity_J(m(D: Mult Set)) = M(D, fn z => z);

fun Source_J_f_J_again(X: Just_for_J_again) = case (X: Just_for_J_again) of M(A,f) => m(A) |MS(B, g) => m(B) |MI(C,h) => m(C) |S(r) => string |II(y) => int;

fun Target_J_f_J_again(i)(X: Just_for_J_again) = case (X: Just_for_J_again) of M(A,f) => if 
	is_subset(imageset(f,A), list_to_set(map(doubles_to_mult)((Customer_List(i))))) then 
			m(list_to_set(map(doubles_to_mult)((Customer_List(i))))) 
							else m(imageset(f,A)) 
	|MS(B,g) => string |MI(C,h) => int |S(r) => string |II(y) => int;
			    

fun JA(i:(string*int) list * (int*int) list * (string * (string*string*int)list) list *(string -> int)) = 
 	fn Ordered => M(INSTANCE_Objects(i)(ORDER), Instance_Func_Mult(i)(KEYVAL))
	|C_Name => MS(list_to_set(map(doubles_to_mult)((Customer_List(i)))), customername)
	|C_Name_Ordered => MS(INSTANCE_Objects(i)(ORDER), customername o Instance_Func_Mult(i)(KEYVAL))
	|C_ID => MI(list_to_set(map(doubles_to_mult)((Customer_List(i)))), customerid) 
	|Cred_lim => MI(list_to_set(map(doubles_to_mult)((Customer_List(i)))), 
		doublecancel o Instance_Func_Mult(i)(CREDITLIMITS)) 
	|P_ID => MS(INSTANCE_Objects(i)(PRODUCT), order_id)
	|P_Name => MS(INSTANCE_Objects(i)(PRODUCT), raw_order_name)  
	|T_Price => MI(INSTANCE_Objects(i)(PRODUCT), price_toint)
	|P_Price => MI(INSTANCE_Objects(i)(ORDER), Total_Price(i))
	|Or_no => MS(INSTANCE_Objects(i)(ORDER), cancel_multO_order)
	|ID(c) => M(list_to_set(map(doubles_to_mult)((Customer_List(i)))), idc)
	|ID(s) => S(ids)
	|ID(I) => II(idi)
	|ID(O) => M(INSTANCE_Objects(i)(ORDER), ido)
	|ID(p) => M(INSTANCE_Objects(i)(PRODUCT), idp);

fun compose_JfJagain(G:Just_for_J_again, F:Just_for_J_again) = case (G:Just_for_J_again, F:Just_for_J_again) of 
	(M(A,g),M(B,f)) => if is_subset(imageset(f,B),A) then M(B, g o f) 
		else raise non_composable_arrows 
	|(MS(C,h),M(D,d)) => if is_subset(imageset(d,D),C) then MS(D, h o d) 
		else raise non_composable_arrows 
	|(MI(W,w),M(E,e)) => if is_subset(imageset(e,E),W) then MI(E, w o e)
		else raise non_composable_arrows 
	|(S(g),MS(V,f)) => MS(V, g o f) |(II(g), MI(Y,f)) => MI(Y, g o f) | (S(y), S(x)) => S(y o x) 	|(II(r), II(t)) => II(r o t);

fun Just_for_J(i) = cat(Source_J_f_J_again, Target_J_f_J_again(i), identity_J, compose_JfJagain);

fun J_Functor(i) = ffunctor(Schema_J, JO(i), JA(i), Just_for_J(i));
	

(* 10.  the RELATIONS *)

fun JCustomer(i) = list_to_set(map(doubles_to_mult)((Customer_List(i))));
fun JOrder(i) = INSTANCE_Objects(i)(ORDER);
fun JProduct(i) = INSTANCE_Objects(i)(PRODUCT);
fun JCredit_limit(i) = doublecancel o Instance_Func_Mult(i)(CREDITLIMITS);
val JPrice = price_toint;
val JProduct_Name = raw_order_name;
val JProduct_ID = order_id;

fun J_KNOWS(i)(a,b) = let val (_,G,_,_) = i in list_member((customerid(a),customerid(b)),G) end;

fun JCustomerJCustomer(i) = cartesian_prod(JCustomer(i),JCustomer(i)); 

fun prodfunction(f) = fn (x,y) => (f(x), f(y)); 

fun Customer_from_int(i)(k) = let val (T,_,_,_) = i in 
	multP(person((k, first(List.nth(T,k))),(k, first(List.nth(T,k))))) end;

fun prod_Customer_from_int(i)(k,l) = let val (T,_,_,_) = i in
	(multP(person((k, first(List.nth(T,k))),(k, first(List.nth(T,k))))),
	multP(person((l, first(List.nth(T,l))),(l, first(List.nth(T,l)))))) end;


fun J_CAN_PAY_PRODUCT(i)(cust, prod) = JCredit_limit(i)(cust) >= 2 * JPrice(prod);

fun J_CAN_PAY_ORDER(i)(cust, ord) = JCredit_limit(i)(cust) >= 2 * Total_Price(i)(ord);

fun filter(pred)(A) = let val (a,A') = singleton_split(A) in if pred(a) then union(singleton(a), filter(pred)(A')) else filter(pred)(A') handle emptysetexception => emptyset end;

fun J_CONTAINS(i)(ord, prod) = 
	let val (_,_,E,_) = i in let val k = Inverse(i)(ord) in 
	list_member((JProduct_ID(prod), JProduct_Name(prod), JPrice(prod)), second(List.nth(E,k))) 	end end;


(*  11: FINALLY, QUERY LANGUAGE *)

datatype JVAR = varC of int | varO of int | varP of int | varI of int | varS of int;

fun createvarsC(0:int) = [] |createvarsC(1:int) = [varC(0)] 
	|createvarsC(k:int) = rev(varC(k-1)::rev(createvarsC(k-2)));
fun createvarsO(0:int) = [] |createvarsO(1:int) = [varO(0)] 
	|createvarsO(k:int) = rev(varO(k-1)::rev(createvarsO(k-2)));
fun createvarsP(0:int) = [] |createvarsP(1:int) = [varP(0)] 
	|createvarsP(k:int) = rev(varP(k-1)::rev(createvarsP(k-2)));
fun createvarsI(0:int) = [] |createvarsI(1:int) = [varI(0)] 
	|createvarsI(k:int) = rev(varI(k-1)::rev(createvarsI(k-2)));
fun createvarsS(0:int) = [] |createvarsS(1:int) = [varS(0)] 
	|createvarsS(k:int) = rev(varS(k-1)::rev(createvarsS(k-2)));

fun createvars(av,bv,cv,dv,ev) = 
	[createvarsC(av), createvarsO(bv), createvarsP(cv), createvarsI(dv), createvarsS(ev)]; 

datatype JCONST = constC of int |constO of string |constP of string |constI of int |constS of string; 

exception nosuchentity of unit;
val nosuchentity_exception = nosuchentity(());

fun create_constC(i)(k:int) = if k>=0 andalso k<Customer_Number(i) then Customer_from_int(i)(k) else
raise nosuchentity_exception;

fun create_constO(i)(" ") = NIL_elem(ORDER) |create_constO(i)(onostring: string) = 
	if list_member(order_no(onostring), Order_List(i)) then multO(order_no(onostring)) 
	else raise nosuchentity_exception;

fun create_constI(k:int) = k;
fun create_constS(exstring: string) = exstring;
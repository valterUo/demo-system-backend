




(* 0: Parts that do not require loading input data *)


fun first(a,b) = a;
fun second(a,b) = b;
fun diag(a) = (a,a);


(* 0.0:  CATEGORY THEORY GENERAL FORMULAS *)



datatype ('o,'a) Cat = cat of ('a -> 'o) * ('a -> 'o) * ('o -> 'a) * (('a * 'a) -> 'a);

datatype ('oA,'aA, 'oB,'aB) Functor 
	= ffunctor of ('oA, 'aA) Cat * ('oA -> 'oB) * ('aA -> 'aB) * ('oB,'aB) Cat;

datatype ('oA,'aA, 'oB,'aB) Nat_Transform 
	= nat_transform of ('oA,'aA, 'oB,'aB) Functor * ('oA -> 'aB) * ('oA,'aA, 'oB,'aB) Functor



(* 0.1:  LIST PROCESSING HELPERS  *)



fun list_member(x,[]) = false |list_member(x,y::L) = x=y orelse list_member(x,L); 

fun list_remove(x,[]) = [] |list_remove(x,[y]) = if x=y then [] else [y] 
	|list_remove(s,z::l) = if s=z then list_remove(s,l) else z::list_remove(s,l);

exception emptylist of unit;
val(emptylist_exception) = emptylist(());

fun is_sublist([],_) = true |is_sublist(e::L,[]) = false |is_sublist([e], L) = list_member(e,L) 
	|is_sublist(e::L, u::M) = if (e=u) then is_sublist(L,M) else is_sublist(e::L,M); 
	
fun canonical_list(~1) = [] |canonical_list(0) = [0] |canonical_list(n) = rev(n::canonical_list(n-1));

fun enumerated_list([],_) = [] |enumerated_list(x::L,k) = (k,x)::enumerated_list(L,k+1);

fun enum_list(L) = enumerated_list(L,0);

fun concat_list([]) = [] |concat_list(x::L') = x @ concat_list(L');

fun listProd xs ys = List.concat(List.map(fn x => List.map(fn y => (x,y)) ys) xs);

fun list_size([]) = 0 |list_size(x::X') = 1+list_size(X');

fun sumlistrec[] = 0 |sumlistrec((j::L):int list) = j+sumlistrec(L);

fun removeduplicates([]) = [] |removeduplicates(y::L) = y::removeduplicates(list_remove(y,L));



(* 0.2: THE CATEGORY FINSET  *)



exception empty_set of unit; 
val emptysetexception = empty_set(());

abstype 'a Set = set of 'a list
	with val emptyset = set([]); 
	fun is_empty(set(s)) = length(s)=0; 
	fun singleton(x) = set([x]); 
	fun union(set(s),set(t)) = set(s@t);
	fun member(x,set(l)) = list_member(x,l); 
	fun remove(x,set(l)) = set(list_remove(x,l)); 
	fun singleton_split(set(nil)) = raise emptysetexception 
	|singleton_split(set(x::s)) = (x, remove(x,set(s))); 
	fun split(s) = let val(x,s') = singleton_split(s) in (singleton(x),s') end 
	end;

fun seteq(A,B) = let val(x,A') = singleton_split(A) in 
			member(x,B) andalso seteq(A',remove(x,B)) end
		 handle emptysetexception => is_empty(A) andalso is_empty(B);

fun is_subset(A,B) = if is_empty(A) then true else 
	let val(x,A')=singleton_split(A) in member(x,B) andalso is_subset(A',B) end;

fun imageset(f,S) = if is_empty(S) then emptyset else 
	let val(x,S') = singleton_split(S) in union(singleton(f(x)),imageset(f,S')) end;

fun list_to_set([]) = emptyset |list_to_set(z::l) = union(singleton(z), list_to_set(l));

fun union_over_list([]) = emptyset |union_over_list(y::l) = union(y, union_over_list(l)); 

fun cardinality(A) = let val (a,A') = singleton_split(A) in 1 + cardinality(A') 
		     handle emptysetexception => 0 end;

fun filter(pred)(A) = let val (a,A') = singleton_split(A) in if pred(a) then union(singleton(a), filter(pred)(A')) else filter(pred)(A') handle emptysetexception => emptyset end;

fun intersection(A,B) = filter (fn b => member(b,A)) B;

datatype 'a Set_Arrow = set_arrow of ('a Set) * ('a -> 'a) * ('a Set);

fun set_arroweq(set_arrow(A,f,B),set_arrow(A',f',B')) =  
	seteq(A,A') andalso seteq(B,B') 
	andalso let val(a,A'') = singleton_split(A) in f(a)=f'(a) 
	andalso set_arroweq(set_arrow(A'',f,B),set_arrow(remove(a,A'),f',B')) end;

fun Set_Extract_Function(set_arrow(_,f,_)) = f;

fun Set_Source(set_arrow(a,_,_)) = a;

fun Set_Target(set_arrow(_,_,c)) = c;

fun Set_Identity(a) = set_arrow(a,fn x=>x,a);

exception non_composable of unit;
val non_composable_arrows = non_composable(());

fun Set_Composition(set_arrow(c,g,d),set_arrow(a,f,b)) = 
	if seteq(b,c) then set_arrow(a, fn x=>g(f(x)),d) else raise non_composable_arrows;

val FinSet = cat(Set_Source,Set_Target,Set_Identity,Set_Composition);

fun cartesian_prod(A,B) = if is_empty(A) then emptyset else 
	let val (a, A') = singleton_split A in 
		union(imageset(fn b => (a,b), B), cartesian_prod(A',B)) end;

fun prod_arrow(set_arrow(A,f,B), set_arrow(C,g,D)) = 
	set_arrow(cartesian_prod(A,C), (fn (x,y) => (f(x),g(y))), cartesian_prod(B,D));

val Diagonalproduct = ffunctor(FinSet, fn A => cartesian_prod(A,A), fn f => prod_arrow(f,f), FinSet);



(* 0.3 The category SCHEMA*)



datatype OBJ = C |S |I |O |P;

datatype ARR = CN |CID |CCL |OC |OPr |OCCID |OCCCL |OID |OCCN |PPr |PID |PN |ID of OBJ;

val SOURCE =
	fn OC => C |CID => I |CCL => I |OCCID => I |OCCCL => I |OPr => I |PPr => I  |CN => S 
	|OCCN => S |OID => S |PID => S |PN => S |ID(C) => C |ID(S) => S |ID(I) => I |ID(O) => O
	|ID(P) => P;

val TARGET = fn
	  OC => O |CID => C |CCL => C |OCCID => O |OCCCL => O |OPr => O |PPr => P  |CN => C 
	|OCCN => O |OID => O |PID => P |PN => P |ID(C) => C |ID(S) => S |ID(I) => I |ID(O) => O
	|ID(P) => P;

fun SCHEMAID(Z) = ID(Z);

fun COMP(g,f) = case (g,f) of 
	 (ID(x),f)  => if TARGET(f) = x then f else raise non_composable_arrows
	|(g,ID(y))  => if SOURCE(g) = y then g else raise non_composable_arrows
	|(OC,CN)    => OCCN |(OC,CID) => OCCID |(OC,CCL) => OCCCL
	|(h,k)      => raise non_composable_arrows;

val SCHEMA = cat(SOURCE, TARGET, SCHEMAID, COMP);

val ARR_fromString = fn 
	  "OC" => OC |"CID" => CID  |"CCL" => CCL |"OCCID" => OCCID |"OCCCL" => OCCCL |"OPr" => OPr |"PPr" => PPr  |"CN" => CN 
	|"OCCN" => OCCN |"OID" => OID |"PID" => PID |"PN" => PN |"ID(C)" => ID(C) |"ID(S)" => ID(S) |"ID(I)" => ID(I) |"ID(O)" => ID(O)
	|"ID(P)" => ID(P);



(* 0.4. Customer, Order and Product datatypes *)



datatype Customer = customer of int * string * int;

fun CustomerID  (customer(a,_,_)) = a;
fun CustomerCL  (customer(_,_,c)) = c;
fun CustomerN   (customer(_,b,_)) = b;

datatype Product = product of string * string * int;

fun ProductID    (product(a,_,_)) = a;
fun ProductN     (product(_,b,_)) = b;
fun ProductPr    (product(_,_,c)) = c;

datatype Order = order of string * (Product list);

fun OrderID(order(a,b)) = a;
fun OrderL(order(a,b)) = b;
fun OrderPr(order(a,b)) = sumlistrec(map(ProductPr) b);

fun CanPayProduct(cust,prod) = CustomerCL(cust) >= ProductPr(prod);
fun CanPayOrder(cust,ord)    = CustomerCL(cust) >= OrderPr(ord);
fun Contains(ord, product(a,b,c)) = list_member(product(a,b,c), OrderL(ord));

datatype Mult = multC of Customer |multO of Order |multP of Product |multI of int |multS of string; 

(* 1.0 Load the data *)

exception noparameter of unit;
val noparameter_exception = noparameter(());
fun removeSome(x: int option) = case (x: int option) of SOME(j) => j |NONE => raise noparameter_exception; 

fun split(delim:char) = fn s1:string => (String.tokens(fn x:char => x = delim)(s1));

fun load_string_int([x,y]) = (x,removeSome(Int.fromString(y)));

fun load_T(s1) = map(load_string_int o split(#":")) (split(#",")(s1));

fun load_G_edge([x,y]) = (removeSome(Int.fromString(x)),removeSome(Int.fromString(y)));

fun load_G(s2) = map(load_G_edge o split(#":")) (split(#",")(s2));

fun llload_s(s4) = map(load_string_int o split(#":")) (split(#",")(s4));

fun lload_s(s4) = fn s'' => (List.nth((List.filter(fn (x,y) => (s''= x))(llload_s(s4))),0));
fun load_s(s4) = fn s'' => second(lload_s(s4)(s''));

val XML_delimiters = fn c:char => (c = #">" orelse c = #"<");
fun order_split(s3) = (String.tokens(XML_delimiters))(s3);
val to_delimiters = fn "Order" => "|" 
	|"/Order" => ""
	|"Orderline" => ","
	|"/Orderline" => ""
	|"Order_no" => ""
	|"/Order_no" => ""
	|"Product_no" => ""
	|"/Product_no" => ""
	|"Product_Name" => ":"
	|"/Product_Name" => ""
	|"Price" => ":"
	|"/Price" => ""
	|x => x;

fun concatenate_stringlist([]) = "" |concatenate_stringlist(x::L) = x^concatenate_stringlist(L);

fun order_rejoin(s3) = concatenate_stringlist(map(to_delimiters)(order_split(s3)));
fun createPreProduct(t) = let val [s1,s2,s3] = split(#":")(t) in (s1,s2,removeSome(Int.fromString(s3))) end;
fun createPreOrder(t') = let val x::L = split(#",")(t') in (x, map(createPreProduct) L) end;
fun createPreOrders(t'') = (map(createPreOrder)(split(#"|")(order_rejoin(t''))));
val load_E = tl o createPreOrders;


fun load(s1,s2,s3,s4) = (load_T(s1),load_G(s2),load_E(s3),load_s(s4));

(* 1.1 Instantiation *)

fun Customer_from_int(j:int,T:(string * int)list) = let val(a,b) = List.nth(T,j) in customer(j,a,b) end;
fun Customer_from_intoption(j': int option, T:(string * int)list) = Customer_from_int(removeSome(j'),T) handle noparameter_exception => customer(~1,"",0);

fun CustomerList(T:(string * int)list) = map(fn j => Customer_from_int(j,T))(canonical_list(list_size(T)-1));

fun CustomerNode(T:(string * int)list) = list_to_set(map(multC)(CustomerList(T)));

fun OrderList(E: (string * (string * string * int) list) list) =
	map(fn (z, L) => order(z, map(product) L)) E;

exception orderproduct of unit;
val orderproduct_exception = orderproduct(());

fun Order_from_onostring(E) = fn onostring => let val ono = (List.filter(fn order(z,L) => z = onostring)(OrderList(E))) in 
	if length(ono) = 1 then multO((List.nth(ono,0))) else raise orderproduct_exception end; 

fun OrderNode(E: (string * (string * string * int) list) list) 
	= list_to_set(map(multO)(OrderList(E)));

fun preProductList(E: (string * (string * string * int) list) list) =
	map(fn (z, L) => map(product) L) E; 

fun ProductList(E: (string * (string * string * int) list) list) = 
	concat_list(preProductList(E));

fun Product_from_PID(E) = fn idstring => let val prdlist = (List.filter(fn p => ProductID(p) = idstring)(ProductList(E))) in if length(prdlist) > 0 then multP(List.nth(prdlist,0)) else raise orderproduct_exception end;

fun Product_from_PN(E) = fn pnstring => let val p'rdlist = (List.filter(fn p => ProductN(p) = pnstring)(ProductList(E))) in if length(p'rdlist) > 0 then multP(List.nth(p'rdlist,0)) else raise orderproduct_exception end;

fun number(p, E) = list_size(ProductList(E)) - list_size(list_remove(p,ProductList(E)));

fun ProductNode(E: (string * (string * string * int) list) list)
	= list_to_set(map(multP)(ProductList(E)));

fun OrdererCustomer(T:(string*int)list, s:string ->int) = fn ord:Order => Customer_from_int(s(OrderID(ord)),T);

fun Mult_from_str
	((T:(string * int)list,G:(int*int)list,E:(string * (string * string * int) list) list, s: string -> int),par:string) 		= fn C => multC(Customer_from_intoption(Int.fromString(par),T))
			|O => Order_from_onostring(E)(par)
			|P => Product_from_PN(E)(par)
			|I => multI(removeSome(Int.fromString(par)))
			|S => multS(par); 

fun namelist(T:(string * int)list) = map(first) T;
fun OIDlist(E:(string * (string * string * int) list) list) = map(OrderID)(OrderList(E));
fun PIDlist(E: (string * (string * string * int) list) list) = map(ProductID)(ProductList(E));
fun PNlist(E: (string * (string * string * int) list) list) = map(ProductN)(ProductList(E));

fun stringList(T,E) = namelist(T) @ OIDlist(E) @ PIDlist(E) @ PNlist(E);
fun stringNode(T,E) = list_to_set(map(multS)(stringList(T,E))); 

fun PPrlist(E: (string * (string * string * int) list) list) = map(ProductPr)(ProductList(E));
fun OPrlist(E: (string * (string * string * int) list) list) = map(OrderPr)(OrderList(E));
fun CCLlist(T:(string * int)list) = map(second) T;
fun CIDlist(T:(string * int)list) = canonical_list(list_size(T)-1);

fun intList(T,E) = PPrlist(E) @ OPrlist(E) @ CCLlist(T) @ CIDlist(T);
fun intNode(T,E) = list_to_set(map(multI)(intList(T,E)));

fun stringNode_fromC(T) = list_to_set(map(multS o CustomerN)(CustomerList(T)));
fun intNode_fromC(T) = list_to_set((map(multI o CustomerCL)(CustomerList(T))) @ (map(multI)(canonical_list(list_size(T)-1))));

fun intNode_fromP(E) = list_to_set(map(multI o ProductPr)(ProductList(E)));
fun stringNode_fromP(E) = list_to_set(map(multS o ProductID)(ProductList(E))@map(multS o ProductN)(ProductList(E)));

fun intNode_fromO(T,E,s) = list_to_set((map(multI o OrderPr)(OrderList(E)) @ map(multI o CustomerID o OrdererCustomer(T,s))(OrderList(E)) @ map(multI o CustomerCL o OrdererCustomer(T,s))(OrderList(E))));

fun stringNode_fromO(T,E,s) = list_to_set((map(multS o OrderID)(OrderList(E)) @ map(multS o CustomerN o OrdererCustomer(T,s))(OrderList(E))));

fun INSTOBJ(T:(string * int)list, G: (int*int)list, E:(string * (string * string * int) list) list, s:string -> int) = fn C => CustomerNode(T) |O => OrderNode(E) |P => ProductNode(E) 
	|I => intNode(T,E) |S => stringNode(T,E);

fun INSTFUNC(T:(string * int)list, G: (int*int)list, E:(string * (string * string * int) list) list, s:string -> int)(x) = case x of 
	CN => (fn multC(c0) => multS(CustomerN(c0)))
	|CID => (fn multC(c0) => multI(CustomerID(c0)))
	|CCL => (fn multC(c0) => multI(CustomerCL(c0)))
	|OC => (fn multO(o0) => multC(OrdererCustomer(T,s)(o0)))
	|OPr => (fn multO(o0) => multI(OrderPr(o0)))
	|OCCID => (fn multO(o0) =>  multI(CustomerID(OrdererCustomer(T,s)(o0))))
	|OCCCL => (fn multO(o0) =>  multI(CustomerCL(OrdererCustomer(T,s)(o0))))
	|OID => (fn multO(o0) => multS(OrderID(o0)))
	|OCCN => (fn multO(o0) =>  multS(CustomerN(OrdererCustomer(T,s)(o0)))) 
	|PPr => (fn multP(p0) => multI(ProductPr(p0)))
	|PID => (fn multP(p0) => multS(ProductID(p0))) 
	|PN => (fn multP(p0) => multS(ProductN(p0)))
	|ID(C) => (fn multC(c0) => multC(c0))
	|ID(O) => (fn multO(o0) => multO(o0))
	|ID(P) => (fn multP(p0) => multP(p0))
	|ID(I) => (fn multI(i0) => multI(i0))
	|ID(S) => (fn multS(s0) => multS(s0));

fun INSTARR(T:(string * int)list, G: (int*int)list, E:(string * (string * string * int) list) list, s:string -> int)(Y) = let val i = (T,G,E,s) in case Y of
	CN => set_arrow(INSTOBJ(i)(C), INSTFUNC(i)(CN), INSTOBJ(i)(S))
	|CID => set_arrow(INSTOBJ(i)(C), INSTFUNC(i)(CID), INSTOBJ(i)(I))
	|CCL => set_arrow(INSTOBJ(i)(C), INSTFUNC(i)(CCL), INSTOBJ(i)(I))
	|OC => set_arrow(INSTOBJ(i)(O), INSTFUNC(i)(OC), INSTOBJ(i)(C))
	|OPr => set_arrow(INSTOBJ(i)(O), INSTFUNC(i)(OPr), INSTOBJ(i)(I))
	|OCCID => set_arrow(INSTOBJ(i)(O), INSTFUNC(i)(OCCID), INSTOBJ(i)(I))
	|OCCCL => set_arrow(INSTOBJ(i)(O), INSTFUNC(i)(OCCCL), INSTOBJ(i)(I))
	|OID => set_arrow(INSTOBJ(i)(O), INSTFUNC(i)(OID), INSTOBJ(i)(S))
	|OCCN => set_arrow(INSTOBJ(i)(O), INSTFUNC(i)(OCCN), INSTOBJ(i)(S)) 
	|PPr => set_arrow(INSTOBJ(i)(P), INSTFUNC(i)(PPr), INSTOBJ(i)(I))
	|PID => set_arrow(INSTOBJ(i)(P), INSTFUNC(i)(PID), INSTOBJ(i)(S))
	|PN => set_arrow(INSTOBJ(i)(P), INSTFUNC(i)(PN), INSTOBJ(i)(S))
	|ID(C) => set_arrow(INSTOBJ(i)(C), INSTFUNC(i)(ID(C)), INSTOBJ(i)(C))
	|ID(O) => set_arrow(INSTOBJ(i)(O), INSTFUNC(i)(ID(O)), INSTOBJ(i)(O))
	|ID(P) => set_arrow(INSTOBJ(i)(P), INSTFUNC(i)(ID(P)), INSTOBJ(i)(P))
	|ID(I) => set_arrow(INSTOBJ(i)(I), INSTFUNC(i)(ID(I)), INSTOBJ(i)(I))
	|ID(S) => set_arrow(INSTOBJ(i)(S), INSTFUNC(i)(ID(S)), INSTOBJ(i)(S)) end;

fun INST(T:(string * int)list, G: (int*int)list, E:(string * (string * string * int) list) list, s:string -> int) = let val i = (T,G,E,s) in ffunctor(SCHEMA, INSTOBJ(i), INSTARR(i), FinSet) end;

(* 1.2. TEST DATASET *)

val preT = "Mary:5000,John:2000,William:3000,Daddy:200,William:30,Erica:8000,Mill:0,Bob:9999";

val preG = "1:6,3:6,6:3,3:1,1:2,0:5,4:2,4:5";

val preE = "<Orders><Order><Order_no>34e5e79</Order_no><Orderline><Product_no>2343f</Product_no><Product_Name>Toy</Product_Name><Price>66</Price></Orderline><Orderline><Product_no>3424g</Product_no><Product_Name>Book</Product_Name><Price>40</Price></Orderline></Order><Order><Order_no>0cbdf508</Order_no><Orderline><Product_no>2543f</Product_no><Product_Name>Guitar</Product_Name><Price>666</Price></Orderline><Orderline><Product_no>1234r</Product_no><Product_Name>Nothing</Product_Name><Price>1</Price></Orderline></Order><Order><Order_no>4dwtfuu</Order_no><Orderline><Product_no>2343f</Product_no><Product_Name>Toy</Product_Name><Price>66</Price></Orderline></Order><Order><Order_no>3qqqeq9</Order_no><Orderline><Product_no>2343f</Product_no><Product_Name>Toy</Product_Name><Price>66</Price></Orderline><Orderline><Product_no>3424g</Product_no><Product_Name>Book</Product_Name><Price>40</Price></Orderline><Orderline><Product_no>3424g</Product_no><Product_Name>Book</Product_Name><Price>40</Price></Orderline><Orderline><Product_no>3424g</Product_no><Product_Name>Book</Product_Name><Price>40</Price></Orderline><Orderline><Product_no>2543f</Product_no><Product_Name>Guitar</Product_Name><Price>666</Price></Orderline></Order><Order><Order_no>77idy65</Order_no><Orderline><Product_no>5467y</Product_no><Product_Name>Pen</Product_Name><Price>2</Price></Orderline><Orderline><Product_no>5698r</Product_no><Product_Name>Car</Product_Name><Price>9999</Price></Orderline></Order><Order><Order_no>ery63rg</Order_no><Orderline><Product_no>7890u</Product_no><Product_Name>Cup</Product_Name><Price>24</Price></Orderline><Orderline><Product_no>5467y</Product_no><Product_Name>Pen</Product_Name><Price>2</Price></Orderline><Orderline><Product_no>3424g</Product_no><Product_Name>Book</Product_Name><Price>40</Price></Orderline><Orderline><Product_no>2543f</Product_no><Product_Name>Guitar</Product_Name><Price>666</Price></Orderline><Orderline><Product_no>896h</Product_no><Product_Name>Jewelry</Product_Name><Price>5000</Price></Orderline><Orderline><Product_no>2343f</Product_no><Product_Name>Toy</Product_Name><Price>66</Price></Orderline></Order></Orders>";

val pres = "34e5e79:1,0cbdf508:2,4dwtfuu:1,3qqqeq9:0,77idy65:3,ery63rg:5"

val preTGEs = (preT, preG, preE, pres);	

val T'' = [("Mary", 5000:int),("John", 2000:int), ("William", 3000:int), ("Daddy", 200:int), ("William", 30:int), ("Erica", 8000:int), ("Mill", 0:int), ("Bob", 9999:int)];
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
		|"4dwtfuu" => 1:int
		|"3qqqeq9" => 0:int
		|"77idy65" => 3:int
		|"ery63rg" => 5:int;

val TESTINPUT = (T'', G'', E'', sq');
val TESTINST = INST(TESTINPUT);
val TESTINSTOBJ = INSTOBJ(TESTINPUT);
val TESTINSTFUNC = INSTFUNC(TESTINPUT);
val TESTINSTARR = INSTARR(TESTINPUT);

fun product_to_string(product(x',y',z')) = "product (" ^ x' ^ "," ^ y' ^ Int.toString(z')^ ")";

fun product_list_to_string(p::L) = if L =[] then product_to_string(p) else 
	product_to_string(p) ^ "\n" ^ product_list_to_string(L)
		handle emptylist_exception => " ";

fun Mult_to_string(multC(customer(x,y,z))) 
	= "customer (" ^ Int.toString(x) ^ "," ^ y ^ "," ^ Int.toString(z) ^ ")"
    |Mult_to_string(multP(product(x',y',z')))
	= product_to_string(product(x',y',z'))
    |Mult_to_string(multO(order(v,H))) = "order (" ^ v ^ "," ^ product_list_to_string(H) ^ ")"
    |Mult_to_string(multI(j)) = "int (" ^ Int.toString(j) ^ ")"
    |Mult_to_string(multS(s)) = "string (" ^ s ^ ")";

fun Mult_list_to_string (m::M) = if M=[] then Mult_to_string(m) else 
	 Mult_to_string(m) ^ "\n" ^ Mult_list_to_string(M)
		handle emptylist_exception => " ";

fun Mult_set_to_string(N) = let val (n,N') = singleton_split(N) in
	if is_empty(N') then Mult_to_string(n) else 
	Mult_to_string(n) ^ "\n" ^ Mult_set_to_string(N') 
		handle emptysetexception => " " end;
	
fun Mult_set_arrow_to_string(set_arrow(A,f,B)) = let val (a,A') = singleton_split(A) in 
	if is_empty(A') then Mult_to_string(a) ^ " : " ^ Mult_to_string(f(a)) else
	Mult_to_string(a) ^ " : " ^ Mult_to_string(f(a)) ^ "\n" ^ 
		Mult_set_arrow_to_string(set_arrow(A',f,B)) handle emptysetexception => " " end;

fun Mult_Mult_to_string(multC(customer(x,y,z)), multC(customer(x',y',z'))) = 
"{" ^ Mult_to_string(multC(customer(x,y,z))) ^ " , " ^ Mult_to_string(multC(customer(x',y',z'))) ^ "}"
	|Mult_Mult_to_string(multC(customer(x,y,z)), multP(product(a',b',c'))) =
"{" ^ Mult_to_string(multC(customer(x,y,z))) ^ " , " ^ Mult_to_string(multP(product(a',b',c'))) ^ "}"
	|Mult_Mult_to_string(multC(customer(x,y,z)), multO(order(v,H))) =
"{" ^ Mult_to_string(multC(customer(x,y,z))) ^ " , " ^ Mult_to_string(multO(order(v,H))) ^ "}"
	|Mult_Mult_to_string(multC(customer(x,y,z)), multI(j)) =
"{" ^ Mult_to_string(multC(customer(x,y,z))) ^ " , " ^ Mult_to_string(multI(j)) ^ "}"
	|Mult_Mult_to_string(multC(customer(x,y,z)), multS(s')) =
"{" ^ Mult_to_string(multC(customer(x,y,z))) ^ " , " ^ Mult_to_string(multS(s')) ^ "}"
	|Mult_Mult_to_string(multP(product(a',b',c')),multC(customer(x,y,z))) =
"{" ^ Mult_to_string(multP(product(a',b',c'))) ^ " , " ^ Mult_to_string(multC(customer(x,y,z))) ^ "}"
	|Mult_Mult_to_string(multO(order(v,H)),multC(customer(x,y,z))) =
"{" ^ Mult_to_string(multO(order(v,H))) ^ " , " ^ Mult_to_string(multC(customer(x,y,z))) ^ "}"
	|Mult_Mult_to_string(multI(j),multC(customer(x,y,z))) =
"{" ^ Mult_to_string(multI(j)) ^ " , " ^ Mult_to_string(multC(customer(x,y,z))) ^ "}"
	|Mult_Mult_to_string(multS(s'),multC(customer(x,y,z))) =
"{" ^ Mult_to_string(multS(s')) ^ " , " ^ Mult_to_string(multC(customer(x,y,z))) ^ "}"
	|Mult_Mult_to_string(multP(product(a',b',c')),multP(product(a'',b'',c''))) =
"{" ^Mult_to_string(multP(product(a',b',c')))^" , "^Mult_to_string(multP(product(a'',b'',c''))) ^ "}"
	|Mult_Mult_to_string(multP(product(a',b',c')),multO(order(v,H))) =
"{" ^ Mult_to_string(multP(product(a',b',c'))) ^ " , " ^ Mult_to_string(multO(order(v,H))) ^ "}"
	|Mult_Mult_to_string(multP(product(a',b',c')),multI(j)) =
"{" ^ Mult_to_string(multP(product(a',b',c'))) ^ " , " ^ Mult_to_string(multI(j)) ^ "}"
	|Mult_Mult_to_string(multP(product(a',b',c')),multS(s')) =
"{" ^ Mult_to_string(multP(product(a',b',c'))) ^ " , " ^ Mult_to_string(multS(s')) ^ "}"
	|Mult_Mult_to_string(multO(order(v,H)),multP(product(a',b',c'))) =
"{" ^ Mult_to_string(multO(order(v,H))) ^ " , " ^ Mult_to_string(multP(product(a',b',c'))) ^ "}"
	|Mult_Mult_to_string(multI(j),multP(product(a',b',c'))) =
"{" ^ Mult_to_string(multI(j)) ^ " , " ^ Mult_to_string(multP(product(a',b',c'))) ^ "}"
	|Mult_Mult_to_string(multS(s'),multP(product(a',b',c'))) =
"{" ^ Mult_to_string(multS(s')) ^ " , " ^ Mult_to_string(multP(product(a',b',c'))) ^ "}"
	|Mult_Mult_to_string(multO(order(v,H)),multO(order(v',H'))) =
"{" ^ Mult_to_string(multO(order(v,H))) ^ " , " ^ Mult_to_string(multO(order(v',H'))) ^ "}"
	|Mult_Mult_to_string(multO(order(v,H)),multI(j)) =
"{" ^ Mult_to_string(multO(order(v,H))) ^ " , " ^ Mult_to_string(multI(j)) ^ "}"
	|Mult_Mult_to_string(multO(order(v,H)),multS(s')) =
"{" ^ Mult_to_string(multO(order(v,H))) ^ " , " ^ Mult_to_string(multS(s')) ^ "}"
	|Mult_Mult_to_string(multI(j),multO(order(v,H))) =
"{" ^ Mult_to_string(multI(j)) ^ " , " ^ Mult_to_string(multO(order(v,H))) ^ "}"
	|Mult_Mult_to_string(multS(s'),multO(order(v,H))) =
"{" ^ Mult_to_string(multS(s')) ^ " , " ^ Mult_to_string(multO(order(v,H))) ^ "}"
	|Mult_Mult_to_string(multS(s'),multS(s'')) =
"{" ^ Mult_to_string(multS(s')) ^ " , " ^ Mult_to_string(multS(s'')) ^ "}"
	|Mult_Mult_to_string(multS(s'),multI(j)) =
"{" ^ Mult_to_string(multS(s')) ^ " , " ^ Mult_to_string(multI(j)) ^ "}"
	|Mult_Mult_to_string(multI(j),multS(s')) =
"{" ^ Mult_to_string(multI(j)) ^ " , " ^ Mult_to_string(multS(s')) ^ "}"
	|Mult_Mult_to_string(multI(j),multI(k)) =
"{" ^ Mult_to_string(multI(j)) ^ " , " ^ Mult_to_string(multI(k)) ^ "}";

fun Mult_Mult_set_to_string(W) = let val ((w1,w2),W') = singleton_split(W) in
	if is_empty(W') then Mult_Mult_to_string((w1,w2)) else 
	Mult_Mult_to_string((w1,w2)) ^ "\n" ^ Mult_Mult_set_to_string(W') 
		handle emptysetexception => " " end;

fun Mult_Mult_set_arrow_to_string(set_arrow(R,g,H)) = let val ((r1,r2),R') = singleton_split(R) in 
	if is_empty(R') then Mult_Mult_to_string((r1,r2)) ^ " : " ^ Mult_Mult_to_string(g((r1,r2)))
		else
	Mult_Mult_to_string((r1,r2)) ^ " : " ^ Mult_Mult_to_string(g((r1,r2))) ^ "\n" ^ 
		Mult_Mult_set_arrow_to_string(set_arrow(R',g,H)) handle emptysetexception => " " end;


val PRINTMULT = print o Mult_to_string;
val PRINTMULT_LIST = print o Mult_list_to_string;
val PRINTMULT_SET = print o Mult_set_to_string; 
val PRINTMULT_SETARROW = print o Mult_set_arrow_to_string;
val PRINTMULT_MULT = print o Mult_Mult_to_string;
val PRINTMULT_MULT_SET = print o Mult_Mult_set_to_string;
val PRINTMULT_MULT_SETARROW = print o Mult_Mult_set_arrow_to_string; 







(* 1.4. Query logic *)


datatype PREDNAME = KNOWS of ARR*ARR | CONTAINS of ARR*ARR | GEQ of ARR*ARR | EQUALS of ARR*ARR;

datatype PARAM = CONSTANT of Mult | VARC of string | VARO of string | VARP of string |VARI of string |VARS of string;

datatype PRED_DATA = pred_data of (PREDNAME * PARAM * PARAM) list;

fun wholeMultSet(T:(string * int)list,G:(int*int)list,E:(string * (string * string * int) list) list, s: string -> int) = 
 	 let val i = (T,G,E,s) in 
	union_over_list([INSTOBJ(i)(C),INSTOBJ(i)(O),INSTOBJ(i)(P),INSTOBJ(i)(I),INSTOBJ(i)(S)])
	end;

fun UNIVERSE(T,G,E,s) = cartesian_prod(wholeMultSet(T,G,E,s),wholeMultSet(T,G,E,s));  

fun isRealMult(T,G,E,s)(m) = member(m,UNIVERSE(T,G,E,s));

fun params_of_predlist(pred_data(L)) = map(fn (a,b,c) => (b,c)) L;
fun preds_of_predlist(pred_data(L)) = map (fn (a,b,c) => a) L;

exception notproperpredicate of unit; 
val notproperpredicate_exception = (());

fun GE(m,m') = case (m,m') of (multI(i1),multI(i2)) => i1 >= i2 |_ => false;

fun GE_PRED(i)(arr1:ARR,arr2:ARR)(m,m') = GE(INSTFUNC(i)(arr1)(m),(INSTFUNC(i)(arr2))(m'));

fun IEQ_PRED(i)(arr1:ARR,arr2:ARR)(m,m') = GE_PRED(i)(arr1:ARR,arr2:ARR)(m,m') andalso GE_PRED(i)(arr1:ARR,arr2:ARR)(m',m); 

fun SEQ_PRED(i)(arr1:ARR,arr2:ARR) = if SOURCE(arr1) = S andalso SOURCE(arr2) = S then 
	fn (m,m') => (INSTFUNC(i)(arr1)(m)=INSTFUNC(i)(arr2)(m')) 
		else fn x => false;


fun translatePredicates(T,G,E,s)= fn
	KNOWS(ID(C),ID(C)) => 
		(fn (multC(customer(x,y,z)), multC(customer(x',y',z'))) => list_member((x,x'),G) |_=> false)
	|KNOWS(ID(C),OC) =>
		(fn (multC(customer(x',y',z')),multO(order(v,L))) => list_member((x',s(v)),G) |_ => false)
	|KNOWS(OC,ID(C)) =>
		(fn (multO(order(v,L)), multC(customer(x',y',z'))) => list_member((s(v),x'),G) |_ => false) 
	|KNOWS(OC,OC) =>
		(fn (multO(order(v',L')),multO(order(v,L))) => list_member((s(v'),s(v)),G) |_ => false)
	|CONTAINS(ID(O),ID(P)) => 
		(fn (multO(ord),multP(product(a,b,c))) => Contains(ord,product(a,b,c)) |_ => false)
	|CONTAINS(ID(P),ID(O)) =>
		(fn (multP(product(a,b,c)),multO(ord)) => Contains(ord,product(a,b,c)) |_ => false)
	|GEQ(ARR1,ARR2) => 
		(fn (m,m') => GE(INSTFUNC(T,G,E,s)(ARR1)(m),INSTFUNC(T,G,E,s)(ARR2)(m')))
	|EQUALS(ARR1,ARR2) => 
		(fn (m,m') => (INSTFUNC(T,G,E,s)(ARR1)(m)=INSTFUNC(T,G,E,s)(ARR2)(m'))); 

fun translate_params(i:(string * int)list * (int*int)list * (string * (string * string * int) list) list *(string -> int)) = fn
	(CONSTANT(m), CONSTANT(m')) => cartesian_prod(singleton(m),singleton(m'))
	|(CONSTANT(m), VARC(str)) => cartesian_prod(singleton(m),INSTOBJ(i)(C))
	|(CONSTANT(m), VARO(str))  => cartesian_prod(singleton(m),INSTOBJ(i)(O))
	|(CONSTANT(m), VARP(str))  => cartesian_prod(singleton(m),INSTOBJ(i)(P))
	|(CONSTANT(m), VARI(str))  => cartesian_prod(singleton(m),INSTOBJ(i)(I))
	|(CONSTANT(m), VARS(str))  => cartesian_prod(singleton(m),INSTOBJ(i)(S))
	|(VARC(str),CONSTANT(m)) => cartesian_prod(INSTOBJ(i)(C),singleton(m))
	|(VARO(str),CONSTANT(m)) => cartesian_prod(INSTOBJ(i)(O),singleton(m))
	|(VARP(str),CONSTANT(m)) => cartesian_prod(INSTOBJ(i)(P),singleton(m))
	|(VARI(str),CONSTANT(m)) => cartesian_prod(INSTOBJ(i)(I),singleton(m))
	|(VARS(str),CONSTANT(m)) => cartesian_prod(INSTOBJ(i)(S),singleton(m))
	|(VARC(str),VARC(str')) => if str=str' then imageset(diag,INSTOBJ(i)(C)) 
		else cartesian_prod(INSTOBJ(i)(C),INSTOBJ(i)(C))
	|(VARO(str),VARO(str')) => if str=str' then imageset(diag,INSTOBJ(i)(O)) 
		else cartesian_prod(INSTOBJ(i)(O),INSTOBJ(i)(O))
	|(VARP(str),VARP(str')) => if str=str' then imageset(diag,INSTOBJ(i)(P)) 
		else cartesian_prod(INSTOBJ(i)(P),INSTOBJ(i)(P))
	|(VARI(str),VARI(str')) => if str=str' then imageset(diag,INSTOBJ(i)(I)) 
		else cartesian_prod(INSTOBJ(i)(I),INSTOBJ(i)(I))
	|(VARS(str),VARS(str')) => if str=str' then imageset(diag,INSTOBJ(i)(S)) 
		else cartesian_prod(INSTOBJ(i)(S),INSTOBJ(i)(S))
	|(VARC(str),VARO(stl)) => cartesian_prod(INSTOBJ(i)(C),INSTOBJ(i)(O))
	|(VARO(str),VARC(stl)) => cartesian_prod(INSTOBJ(i)(O),INSTOBJ(i)(C))
	|(VARC(str),VARP(stl)) => cartesian_prod(INSTOBJ(i)(C),INSTOBJ(i)(P))
	|(VARP(str),VARC(stl)) => cartesian_prod(INSTOBJ(i)(P),INSTOBJ(i)(C))
	|(VARC(str),VARI(stl)) => cartesian_prod(INSTOBJ(i)(C),INSTOBJ(i)(I))
	|(VARI(str),VARC(stl)) => cartesian_prod(INSTOBJ(i)(I),INSTOBJ(i)(C))
	|(VARC(str),VARS(stl)) => cartesian_prod(INSTOBJ(i)(C),INSTOBJ(i)(S))
	|(VARS(str),VARC(stl)) => cartesian_prod(INSTOBJ(i)(S),INSTOBJ(i)(C))
	|(VARP(str),VARO(stl)) => cartesian_prod(INSTOBJ(i)(P),INSTOBJ(i)(O))
	|(VARO(str),VARP(stl)) => cartesian_prod(INSTOBJ(i)(O),INSTOBJ(i)(P))
	|(VARP(str),VARI(stl)) => cartesian_prod(INSTOBJ(i)(P),INSTOBJ(i)(I))
	|(VARI(str),VARP(stl)) => cartesian_prod(INSTOBJ(i)(I),INSTOBJ(i)(P))
	|(VARP(str),VARS(stl)) => cartesian_prod(INSTOBJ(i)(P),INSTOBJ(i)(S))
	|(VARS(str),VARP(stl)) => cartesian_prod(INSTOBJ(i)(S),INSTOBJ(i)(P))
	|(VARO(str),VARI(stl)) => cartesian_prod(INSTOBJ(i)(O),INSTOBJ(i)(I))
	|(VARI(str),VARO(stl)) => cartesian_prod(INSTOBJ(i)(I),INSTOBJ(i)(O))
	|(VARO(str),VARS(stl)) => cartesian_prod(INSTOBJ(i)(O),INSTOBJ(i)(S))
	|(VARS(str),VARO(stl)) => cartesian_prod(INSTOBJ(i)(S),INSTOBJ(i)(O))
	|(VARS(str),VARI(stl)) => cartesian_prod(INSTOBJ(i)(S),INSTOBJ(i)(I))
	|(VARI(str),VARS(stl)) => cartesian_prod(INSTOBJ(i)(I),INSTOBJ(i)(S));

fun SOLSET((T:(string * int)list,G:(int*int)list,E:(string * (string * string * int) list) list, s: string -> int), Pred:(Mult*Mult -> bool)) = filter(Pred)(UNIVERSE(T,G,E,s));


	

fun longlist((T:(string * int)list,G:(int*int)list,E:(string * (string * string * int) list) list, 
	s: string -> int)) = 
		map(multC)(CustomerList(T)) @ map(multO)(OrderList(E)) 
		@ removeduplicates(map(multP)(ProductList(E))) @ map(multI)(intList(T,E)) 
		@ map(multS)(stringList(T,E));


fun SOL_LIST((T:(string * int)list,G:(int*int)list,E:(string * (string * string * int) list) list, s: string -> int), Pred:(Mult*Mult -> bool)) 
	= List.filter Pred (listProd(longlist(T,G,E,s))(longlist(T,G,E,s)));

fun SOLUTION_SET((T,G,E,s),Pn:PREDNAME,par1:PARAM,par2:PARAM) 
	= intersection(SOLSET((T,G,E,s),(translatePredicates(T,G,E,s)(Pn))),
			translate_params(T,G,E,s)(par1,par2));


	

(* 1.3. Query input string parsing *)

fun split1(ui) = split(#"|")(ui);

fun organize(ui) = List.partition(fn s' => (String.isPrefix("EQ:")(s')))(split1(ui)); 
fun organize1(ui) = let val (L,R) = organize(ui) in 
	if null(R) then (L,[],[]) else 
		let val (R1,R2) = List.partition(fn s' => (String.isPrefix("GE:")(s')))(R) in
			(L,R1,R2) end end;

fun organize2(L,R1,R2) = let val (R',R'') = List.partition(fn s' => (String.isPrefix("CO:")(s')))(R2) in (L,R1,R',R'') end;

fun to4list(l) = let val L = map(tl o split(#":"))(l) in map(split(#","))(List.concat(L)) end;

fun organize3(L1,L2,L3,L4) = (to4list(L1),to4list(L2),to4list(L3),to4list(L4));

fun params([a,b,c,d]) = (b,d);
fun collectparams(L) = map(params) L;
fun paramlist(i)(ui) = let val (R1,R2,R3,R4) = (organize3(organize2(organize1(ui)))) in
	(collectparams R1, collectparams R2, collectparams R3, collectparams R4) end;

fun parse_GE_pred(i)([arr1,b,arr2,d]) = GE_PRED(i)(ARR_fromString(arr1),ARR_fromString(arr2)); 





(* 1.5. Query answer output parsing *)

fun toIdentifiers(multC(customer(a,c,b))) = Int.toString(a) |toIdentifiers(multO(order(v,L))) = v
	|toIdentifiers(multP(product(x,y,z))) = y |toIdentifiers(multI(j)) = Int.toString(j)
	|toIdentifiers(multS(s')) =s';

fun toStringDelim(delimstr) = fn [] => "" |x::L => x^delimstr^((toStringDelim(delimstr))(L));

fun solution_list_toString(sollist: Mult list list) = 
	toStringDelim(",")((map(toStringDelim(":"))((map(fn l => (map(toIdentifiers)(l)))(sollist)))));

fun graph_arrow_toString(m,m') = toIdentifiers(m)^":"^toIdentifiers(m');

fun solution_graph_toString(solgraph: (Mult*Mult) list) = toStringDelim(",")((map(graph_arrow_toString)(solgraph))); 
/* ------ */
/* Aux DS */
/* ------ */

/* map union by Tim Wood */
function union<U, V>(m: map<U,V>, m'': map<U,V>): map<U,V>
	requires m !! m''; // disjoint
	ensures forall i :: i in union(m, m'') <==> i in m || i in m'';
	ensures forall i :: i in m ==> union(m, m'')[i] == m[i];
	ensures forall i :: i in m'' ==> union(m, m'')[i] == m''[i];
{
	map i | i in (domain(m) + domain(m'')) :: if i in m then m[i] else m''[i]
}

function domain<U,V>(m: map<U,V>) : set<U>
	ensures domain(m) == set u : U | u in m :: u;
	ensures forall u :: u in domain(m) ==> u in m;
{
	set u : U | u in m :: u
}

/* Def. Pair */
datatype prod<A, B> = pair(fst:A, snd:B);

function first<A, B>(p: prod<A, B>): A
{
	match p
		case pair(fst, snd) => p.fst
}

function second<A, B>(p: prod<A, B>): B
{
	match p
		case pair(fst, snd) => p.snd
}
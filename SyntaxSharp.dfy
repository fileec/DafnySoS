
/* ------ */
/* Syntax */
/* ------ */


datatype Dtype = Dunit | Dint | Dbool; 					/* Def. Data type */
datatype Val = Vnull | Vint(i: int) | Vbool(b: bool);	/* Def. Value */

datatype Mident = Ref(v: int); 							/* mutable identifier */
datatype Ident = Var(v: int); 							/* local identifier */



/* Def. binary operator */
datatype operator =  
  Oplus 
| Ominus 
| Omulti 
| Ole;

/* Def. expression */
datatype term = 
  Tmvalue(v: Val) 
| Tmvar(id: Ident) 
| Tmderef(ref: Mident) 
| Tmbin(op1: term, op2:term, op: operator);

/* Def. logical expression */
datatype fmla = 
  Fterm(t: term) 
| Fand(a1: fmla, a2: fmla) 
| Fnot(n1: fmla) 
| Fimplies(i1: fmla, i2: fmla) 
| Flet(id: Ident, expr: term, fm: fmla)
| Fforall(v: Ident, ty: Dtype, f1: fmla);


/* Def. program statement */
datatype stmt = 
  Sskip 
| Sassign(id: Mident, expr: term) 
| Sseq(s1: stmt, s2: stmt) 
| Sif(grd: term, thn: stmt, els: stmt) 
| Sassert(fm: fmla) 
| Swhile(cond: term, inv: fmla, body: stmt);





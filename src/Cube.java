
import java.util.*;

import com.microsoft.z3.*;
public class Cube {
	public final Set<Expr> pos;
	public final Set<Expr> neg;
	public Context ctx;
	
	public Cube(Set<Expr> p, Set<Expr> n, Context c){
		this.pos = p;
		this.neg = n;
		this.ctx = c;
	}
	
	public Expr toExpr(){
		Integer s = pos.size()+neg.size();
		BoolExpr[] args = new BoolExpr[s];
		Integer i = 0;
		for(Expr e: pos){
			args[i] = (BoolExpr) e;
			i++;
		}
		for(Expr e: neg){
			args[i] = ctx.mkNot((BoolExpr) e);
			i++;
		}
		return ctx.mkAnd(args);
	}
	
	public Clause negate(){
		return new Clause(neg, pos, ctx);
	}

	public Cube prime(){
		Set<Expr> posargs = new HashSet<Expr>();
		Set<Expr> negargs = new HashSet<Expr>();
		for(Expr e: pos){
				posargs.add(ctx.mkBoolConst(e.getFuncDecl().getName().toString() + "\'"));
		}
		for(Expr e: neg){
				negargs.add(ctx.mkBoolConst(e.getFuncDecl().getName().toString() + "\'"));
		}
		return new Cube(posargs, negargs, ctx);
	}
	
	public boolean isPrime(Expr var){
		return var.getFuncDecl().getName().toString().endsWith("\'");
	}
	
	public Set<Expr> getVars(){
		Set<Expr> result = new HashSet<Expr>();
		for(Expr e: pos)
			result.add(e);
		for(Expr e: neg)
			result.add(e);
		return result;
	}	
	
	public Interpretation toInterpretation(){
		Map<Symbol, Boolean> map = new HashMap<>();
		pos.stream().forEach(v -> map.put(v.getFuncDecl().getName(), true));
		neg.stream().forEach(v -> map.put(v.getFuncDecl().getName(), false));
		return new Interpretation(map);
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((neg == null) ? 0 : neg.hashCode());
		result = prime * result + ((pos == null) ? 0 : pos.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (!(obj instanceof Cube)) {
			return false;
		}
		Cube other = (Cube) obj;
		if (neg == null) {
			if (other.neg != null) {
				return false;
			}
		} else if (!neg.equals(other.neg)) {
			return false;
		}
		if (pos == null) {
			if (other.pos != null) {
				return false;
			}
		} else if (!pos.equals(other.pos)) {
			return false;
		}
		return true;
	}
	
	@Override
	public String toString() {
		return toExpr().toString();
	}
	
	public Cube removePrime() {
		Set<Expr> posargs = new HashSet<Expr>();
		Set<Expr> negargs = new HashSet<Expr>();
		for(Expr e: pos){
			if(!e.getFuncDecl().getName().toString().endsWith("\'"))
				posargs.add(e);
		}
		for(Expr e: neg){
			if(!e.getFuncDecl().getName().toString().endsWith("\'"))
				negargs.add(e);
		}
		return new Cube(posargs, negargs, ctx);
	}
}

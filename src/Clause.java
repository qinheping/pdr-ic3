import java.util.*;

import com.microsoft.z3.*;
public class Clause {
	public final Set<Expr> pos;
	public final Set<Expr> neg;
	public Context ctx;
	
	public Clause(Set<Expr> p, Set<Expr> n, Context c){
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
		return ctx.mkOr(args);
	}
	
	public Cube negate(){
		return new Cube(neg, pos, ctx);
	}
	
	public Clause prime(){
		Set<Expr> posargs = new HashSet<Expr>();
		Set<Expr> negargs = new HashSet<Expr>();
		for(Expr e: pos){
			posargs.add(ctx.mkBoolConst(e.getFuncDecl().getName().toString() + "\'"));
		}
		for(Expr e: neg){
			if(isPrime(e))
				negargs.add(ctx.mkBoolConst(e.getFuncDecl().getName().toString() + "\'"));
		}
		return new Clause(posargs, negargs, ctx);
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
	
	public Clause remove(Symbol var){
		Set<Expr> posargs = new HashSet<Expr>();
		Set<Expr> negargs = new HashSet<Expr>();
		for(Expr e: pos){
			if(!e.getFuncDecl().getName().toString().equals(var.toString()))
			posargs.add(ctx.mkBoolConst(e.getFuncDecl().getName().toString()));
		}
		for(Expr e: neg){
			if(!e.getFuncDecl().getName().toString().equals(var.toString()))
			negargs.add(ctx.mkBoolConst(e.getFuncDecl().getName().toString()));
		}
		return new Clause(posargs, negargs, ctx);
	}
	
	public boolean isSubclauseOf(Clause other) {
		return pos.stream().allMatch(other.pos::contains)
				&& neg.stream().allMatch(other.neg::contains);
	}
	
	@Override
	public String toString() {
		return toExpr().toString();
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
		if (!(obj instanceof Clause)) {
			return false;
		}
		Clause other = (Clause) obj;
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
}

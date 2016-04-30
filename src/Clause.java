import java.util.*;

import com.microsoft.z3.*;
public class Clause {
	public final Set<BoolExpr> exprs;
	public Context ctx;
	
	public Clause(Set<BoolExpr> n, Context c){
		this.exprs = n;
		this.ctx = c;
	}
	
	public BoolExpr toExpr(){
		Integer s = exprs.size();
		BoolExpr[] args = new BoolExpr[s];
		Integer i = 0;
		for(BoolExpr e: exprs){
			args[i] = e;
			i++;
		}
		return ctx.mkOr(args);
	}
	
	public Cube negate(){
		Set<BoolExpr> args = new HashSet<BoolExpr>();
		for(BoolExpr e: exprs){
			args.add(ctx.mkNot(e));
		}
		return new Cube(args, ctx);
	}
	
	public Clause prime(){
		Set<BoolExpr> args = new HashSet<BoolExpr>();
		for(BoolExpr e: exprs){
			int notcount = 0;
			BoolExpr t = e;
			while(t.getNumArgs() == 1){
				t = (BoolExpr) t.getArgs()[0];
				notcount++;
			}
			Expr varprime = ctx.mkConst(t.getArgs()[0].getFuncDecl().getName().toString() + "\'", t.getArgs()[0].getSort());
			BoolExpr eprime = ctx.mkEq(varprime, t.getArgs()[1]);
			while(notcount > 0){
				eprime = ctx.mkNot(eprime);
				notcount--;
			}
			args.add(eprime);
		}
		return new Clause(args, ctx);
	}
	
	public boolean isPrime(BoolExpr e){
		int notcount = 0;
		BoolExpr t = e;
		while(t.getNumArgs() == 1){
			t = (BoolExpr) t.getArgs()[0];
			notcount++;
		}
		return t.getArgs()[0].getFuncDecl().getName().toString().endsWith("\'");
	}
	
	public Set<Symbol> getVars(){
		Set<Symbol> result = new HashSet<Symbol>();
		for(BoolExpr e: exprs){
			int notcount = 0;
			BoolExpr t = e;
			while(t.getNumArgs() == 1){
				t = (BoolExpr) t.getArgs()[0];
				notcount++;
			}
			result.add(t.getArgs()[0].getFuncDecl().getName());
			}
		return result;
	}
	
	public Clause remove(Symbol var){
		Set<BoolExpr> args = new HashSet<BoolExpr>();
		for(BoolExpr e: exprs){
			int notcount = 0;
			BoolExpr t = e;
			while(t.getNumArgs() == 1){
				t = (BoolExpr) t.getArgs()[0];
				notcount++;
			}
			if(!t.getArgs()[0].getFuncDecl().getName().toString().equals(var.toString()))
				args.add(e);
		}
		return new Clause(args, ctx);
	}
	
	public boolean isSubclauseOf(Clause other) {
		return exprs.stream().allMatch(other.exprs::contains);
	}
	
	@Override
	public String toString() {
		return toExpr().toString();
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((exprs == null) ? 0 : exprs.hashCode());
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
		if (exprs == null) {
			if (other.exprs != null) {
				return false;
			}
		} else if (!exprs.equals(other.exprs)) {
			return false;
		}
		return true;
	}
}
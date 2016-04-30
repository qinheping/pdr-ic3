import java.util.*;

import com.microsoft.z3.*;

public class Trace {
	private final Expr expr;
	private final Set<Clause> clauses = new HashSet<>();
	public Context ctx;
	
	public Trace(Expr expr, Context ctx){
		this.expr = expr;
		this.ctx = ctx;
	}
	public Trace(Context ctx){
		this.ctx = ctx;
		this.expr = ctx.mkTrue();
	}
	
	public Set<Clause> getClauses() {
		return clauses;
	}

	public Expr toExpr(){
		int size = clauses.size();
		BoolExpr[] args = new BoolExpr[size+1];
		args[0] = (BoolExpr) expr;
		int i = 1;
		for(Clause c: clauses){
			args[i] = (BoolExpr) c.toExpr();
			i++;
		}
		return ctx.mkAnd(args);
	}
	
	public void addClause(Clause incoming) {
		Iterator<Clause> iter = clauses.iterator();
		while (iter.hasNext()) {
			Clause existing = iter.next();
			if (incoming.isSubclauseOf(existing) && !incoming.equals(existing)) {
				System.err.println("Replacing " + existing + " with " + incoming);
				iter.remove();
			}
		}
		clauses.add(incoming);
	}
	
	@Override
	public String toString() {
		return expr.toString() + " " + clauses.toString();
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((clauses == null) ? 0 : clauses.hashCode());
		result = prime * result + ((expr == null) ? 0 : expr.hashCode());
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
		if (!(obj instanceof Trace)) {
			return false;
		}
		Trace other = (Trace) obj;
		if (clauses == null) {
			if (other.clauses != null) {
				return false;
			}
		} else if (!clauses.equals(other.clauses)) {
			return false;
		}
		if (expr == null) {
			if (other.expr != null) {
				return false;
			}
		} else if (!expr.equals(other.expr)) {
			return false;
		}
		return true;
	}
}


import java.util.*;
import java.util.Map.Entry;

import com.microsoft.z3.*;
public class PDR {
	private final List<Trace> F = new ArrayList<>();		// F_0 F_1 ... F_N
	private final Map<Cube,Cube> chains = new HashMap<>();	// a ordered list of cube from I to negP
	private Context ctx;									// counter used by z3
	private Integer N = 0;									// phase counter
	protected final Expr I;									// initial state
	protected final BoolExpr T;								// transition formula
	protected final Expr P;									// safe property
	

	// Main entrance, return conterexamples if violet
	public List<Interpretation> check(){
		F.add(new Trace(I,ctx));	// F_0 = I, initial first trace
		try{
		while(true){
			
			// query: (F_N /\ (neg P)) in phase N
			Expr query = ctx.mkAnd((BoolExpr)F.get(N).toExpr(),ctx.mkNot((BoolExpr) P));
			Optional<Model> result = check(ctx,(BoolExpr) query,Status.SATISFIABLE);
			// if there exists some m such that m-> (F_N /\ (neg P))
			if(result.isPresent()){
				// Candidate
				Model mo = result.get();
				Cube m = ModeltoCube(mo);
				Cube t = generalizeSat(m, query);	// restrict m on query
				block(t, N);						// decide to block or not
			} else {
				// Unfold
				// Induction
				propagateClauses();			
				
				// Unreachable return empty list
				if (existsEqualFrames()) {
					return Collections.emptyList();
				}
				 
				// initialize F_{N+1} := TRUE
				F.add(new Trace(ctx));
				
				// go to next phase
				N++;
			}
		}}catch (Counterexample cex) {
			return cex.cex;
		}
	}
	
	private boolean existsEqualFrames() {
		for (int k = 1; k < N; k++) {
			if (F.get(k).equals(F.get(k + 1))) {
				return true;
			}
		}
		return false;
	}
	
	private void propagateClauses() {
		for (int k = 1; k < N; k++) {
			// for any clause in first N phases
			for (Clause c : F.get(k).getClauses()) {
				// propagate c if T(F_k,)
				Expr query = ctx.mkAnd((BoolExpr)F.get(k).toExpr(), (BoolExpr)T, (BoolExpr)c.prime().toExpr());
				Optional<Model> res = check(ctx,(BoolExpr) query,Status.SATISFIABLE);
				if (!res.isPresent()) {
					F.get(k + 1).addClause(c);
				}
			}
		}
	}
	
	// This method decide to block a cube or not
	private void block(Cube m0, Integer k0){
		// each obligation is a pair of (m,k) where s violet P in N-k steps
		PriorityQueue<Obligation> Q = new PriorityQueue<>();
		Q.add(new Obligation(m0, k0));

		while(!Q.isEmpty()){
			// chose (m,k) with largest k
			Obligation en = Q.poll();
			Cube m = (Cube) en.s;
			int k = en.k;
			
			// return counter example if (m,0) in Q
			if(k == 0){
				if(check(ctx,(BoolExpr) ctx.mkAnd(CubetoExpr(m),(BoolExpr)I),Status.SATISFIABLE).isPresent())
					extractCounterexample(m);
			} else {
				// for pair of (m,k) check whether T(F_{k-1} /\ neg m) -> neg m'
				Expr query = ctx.mkAnd((BoolExpr)F.get(k-1).toExpr(), ctx.mkNot((BoolExpr) m.toExpr()), T, (BoolExpr)m.prime().toExpr());
				Optional<Model> result = check(ctx,(BoolExpr) query,Status.SATISFIABLE);
				if(result.isPresent()){
					// Decide
					Cube t = generalizeSat(ModeltoCube(result.get()), query).removePrime();
					chains.put(t, m);
					Q.add(new Obligation(t, k - 1));
					Q.add(new Obligation(m, k));
				} else{
					// Conflict
					Clause t = generalizeUnsat(m.negate(), ctx.mkAnd((BoolExpr)F.get(k-1).toExpr(), T));
					for (int i = 1; i <= k; i++) {
						F.get(i).addClause(t);
					}

					// Original cube is bad in future states too
					if (k < N) {
						Q.add(new Obligation(m, k + 1));
					}
				}
			}
		}
	}
	
	// Inductively generalize 'clause' with respect to 'relative'
	private Clause generalizeUnsat(Clause clause, Expr relative) {
		Clause curr = clause;

		for (Expr v : clause.getVars()) {
			Clause reduced = curr.remove(v.getFuncDecl().getName());

			// clause cannot overlap initial states
			if (check(ctx, ctx.mkAnd((BoolExpr)I, (BoolExpr)curr.toExpr()),Status.SATISFIABLE).isPresent()) {
				continue;
			}

			Expr query = ctx.mkAnd((BoolExpr)relative, (BoolExpr)curr.toExpr(), (BoolExpr)curr.negate().prime().toExpr());
			if (!check(ctx, (BoolExpr)query,Status.SATISFIABLE).isPresent()) {
				curr = reduced;
			}
		}

		if (curr != clause) {
			System.out.println("Before: " + clause);
			System.out.println("After: " + curr);
			System.out.println();
		}

		return curr;
	}
	
	// Construct counter example from cube s
	private void extractCounterexample(Cube s) {
		List<Interpretation> args = new ArrayList<>();
		// at the beginning  current cube s is in I
		Cube curr = s;
		while (curr != null) {
			args.add(curr.toInterpretation());
			curr = chains.get(curr);
		}
		throw new Counterexample(args);
	}
	
	// Constrain Cube c on Expr query
	private Cube generalizeSat(Cube c, Expr query){
		Interpretation interp = c.toInterpretation();
		
		// constrain interp on query, that is, deleting 
		for (Expr v: c.getVars()){

			// if a var is not prime
			if(!v.getFuncDecl().getName().toString().substring(v.getFuncDecl().getName().toString().length() - 1).equals('\'')){
				Interpretation reduced = interp.remove(v.getFuncDecl().getName());
				interp = reduced;
			}
		}
		return InterptoCube(interp);
	}
	
	// Convert an interpretation to a Z3 Expr, such that the Expr is ture <=> all var are assigned as the given interp
	public BoolExpr InterptoExpr(Map<Symbol,Boolean> interp){
		Expr result = null;
		Expr t = ctx.mkTrue();
		Expr f = ctx.mkFalse();
		Integer size = interp.size();
		Integer i = 0;
		Expr[] args = new Expr[size];
		for(Symbol s: interp.keySet()){
			if(interp.get(s))
				args[i] = ctx.mkEq(ctx.mkBoolConst(s), t);
			else
				args[i] = ctx.mkEq(ctx.mkBoolConst(s), f);
			i++;
		}
		return ctx.mkAnd((BoolExpr[]) args);
	}
	
	// Convert an interpretation to a Cube
	public Cube InterptoCube(Interpretation interp){
		Set<Expr> positives = new HashSet<>();
		Set<Expr> negatives = new HashSet<>();
		Map<Symbol, Boolean> map = interp.map;
		for (Symbol s : map.keySet()) {
			if (map.get(s)) {
				positives.add(ctx.mkBoolConst(s));
			} else {
				negatives.add(ctx.mkBoolConst(s));
			}
		}
		return new Cube(positives, negatives,ctx);
	}
	
	// Convert a Cube to a Z3 Expr
		public BoolExpr CubetoExpr(Cube c){
			Set<Expr> positives = c.pos;
			Set<Expr> negatives = c.neg;
			Integer size = positives.size() + negatives.size();
			BoolExpr[] args = new BoolExpr[size];
			Integer i = 0;
			for(Expr e: positives){
				args[i] = ctx.mkBoolConst(e.getFuncDecl().getName());
				i++;
			}
			for(Expr e: negatives){
				args[i] = ctx.mkNot(ctx.mkBoolConst(e.getFuncDecl().getName()));
				i++;
			}
			return ctx.mkAnd(args);
		}
	
    Optional<Model> check(Context ctx, BoolExpr f, Status sat)
    {
        Solver s = ctx.mkSolver();
        s.add(f);
        if (s.check() != sat)
            return Optional.empty();
        if (sat == Status.SATISFIABLE)
            return Optional.of(s.getModel());
        else
            return Optional.empty();
    }
    
	public PDR(Expr I, BoolExpr T, Expr P, Context ctx){
		this.I = I;
		this.T = T;
		this.P = P;
		this.ctx = ctx;
	}
	
	public Cube ModeltoCube(Model mo){
		Set<Expr> positives = new HashSet<>();
		Set<Expr> negatives = new HashSet<>();
		for(FuncDecl f: mo.getConstDecls()){
			if(mo.getConstInterp(f).isTrue()){
				positives.add(ctx.mkBoolConst(f.getName()));
			}else
				negatives.add(ctx.mkBoolConst(f.getName()));
		}
		return new Cube(positives,negatives,ctx);
	}
	
	// Check whether all vars in interp appear in query
	public boolean checkPresent(Expr query, Map<Symbol,Boolean> interp){
		boolean flag;							
		for(Symbol s: interp.keySet()){
			flag = false;		
			for(Expr e: query.getArgs()){
				if(s.toString().equals(e.getFuncDecl().getName().toString()))
					flag = true;												// we found a s in e so turn flag to true
			}
			if(!flag)															// return false when s not in e
				return false;
		}
		return true;
	}
	
	// Check whether an interpretation satisfy a given query
	public boolean check(Expr query, Map<Symbol,Boolean> interp){
		Solver s = ctx.mkSolver();
        s.add(ctx.mkAnd((BoolExpr)query,InterptoExpr(interp)));
        if (s.check() == Status.SATISFIABLE)
            return true;
        else
        	return false;
	}
	
	public void showFrames() {
		for (int k = 1; k <= N; k++) {
			System.out.println("Frame " + k + ": " + F.get(k));
		}
	}	
}

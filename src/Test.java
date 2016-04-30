import static org.junit.Assert.*;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import com.microsoft.z3.*;

public class Test {

	/*
	 *  test1:
	 *  	I = (-a)(-b)
	 *  	T = (-a',-a)(a',a)(b',a,-b)(b',-a,b)(-b',a,b)(-b',-a,-b) : a'=-a, b'=a xor b
	 *  	P = (-a,-b)
	 */
	@org.junit.Test
	public void test1() {
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        
        BoolExpr a = ctx.mkBoolConst("a");
        BoolExpr b = ctx.mkBoolConst("b");
        
        BoolExpr I = ctx.mkNot(ctx.mkOr(a, b));
        
        BoolExpr Ta = ctx.mkEq(toPrime(a, ctx), ctx.mkNot(a));
        BoolExpr Tb = ctx.mkEq(toPrime(b, ctx), ctx.mkXor(b,a));
        BoolExpr T = ctx.mkAnd(Ta, Tb);
        
        Expr P = ctx.mkNot(ctx.mkAnd(a, b));
        
       // check(I,T, P, ctx);
	}
	
	/*
	 *  test2:
	 *  	I = (a)(b)(-c)
	 *  	T = (-a,c')(a,-c')(b,-b')(-a,-b,-a')(-c,a',a)(-c,a',b)
	 *  	P = (-a,-b,-c)
	 */
	@org.junit.Test
	public void test2() {
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        
        BoolExpr a = ctx.mkBoolConst("a");
        BoolExpr b = ctx.mkBoolConst("b");
        BoolExpr c = ctx.mkBoolConst("c");
        
        BoolExpr I = ctx.mkNot(ctx.mkOr(ctx.mkNot(a), ctx.mkNot(b), c));
        
        BoolExpr T1 = ctx.mkOr(ctx.mkNot(a), toPrime(c, ctx));
        BoolExpr T2 = ctx.mkOr(a, ctx.mkNot(toPrime(c, ctx)));
        BoolExpr T3 = ctx.mkOr(b, ctx.mkNot(toPrime(b, ctx)));
        BoolExpr T4 = ctx.mkOr(ctx.mkNot(a),ctx.mkNot(b), ctx.mkNot(toPrime(a, ctx)));
        BoolExpr T5 = ctx.mkOr(ctx.mkNot(c),a, toPrime(a, ctx));
        BoolExpr T6 = ctx.mkOr(ctx.mkNot(c),b, toPrime(a, ctx));
        BoolExpr T = ctx.mkAnd(T1,T2,T3,T4,T5,T6);
        
        Expr P = ctx.mkNot(ctx.mkAnd(a, b, c));
        
        //check(I,T, P, ctx);
	}
	
	/*
	 *  test3:
	 *  	I = (a)(b)(-c)
	 *  	T = (-a,c')(a,-c')(b,-b')(-a,-b,-a')(-c,a',a)(-c,a',b)
	 *  	P = (a,b,c)
	 */
	@org.junit.Test
	public void test3() {
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        
        BoolExpr a = ctx.mkBoolConst("a");
        BoolExpr b = ctx.mkBoolConst("b");
        BoolExpr c = ctx.mkBoolConst("c");
        
        BoolExpr I = ctx.mkNot(ctx.mkOr(ctx.mkNot(a), ctx.mkNot(b), c));
        
        Expr t = ctx.mkEq(ctx.mkIntConst("d"), ctx.mkInt(5));
        
        BoolExpr T1 = ctx.mkOr(ctx.mkNot(a), toPrime(c, ctx));
        BoolExpr T2 = ctx.mkOr(a, ctx.mkNot(toPrime(c, ctx)));
        BoolExpr T3 = ctx.mkOr(b, ctx.mkNot(toPrime(b, ctx)));
        BoolExpr T4 = ctx.mkOr(ctx.mkNot(a),ctx.mkNot(b), ctx.mkNot(toPrime(a, ctx)));
        BoolExpr T5 = ctx.mkOr(ctx.mkNot(c),a, toPrime(a, ctx));
        BoolExpr T6 = ctx.mkOr(ctx.mkNot(c),b, toPrime(a, ctx));
        BoolExpr T = ctx.mkAnd(T1,T2,T3,T4,T5,T6);
        
        Expr P = ctx.mkOr(a, b, c);
        
        //check(I,T, P, ctx);
	}
	
	/*
	 *  test4:
	 *  	I = (a)(-b)(-c)
	 *  	T = (-a,c')(a,-c')(b,-a')(-b,a')(-c,b')(-c,b)
	 *  		: a' = b; b' = c; c' = a;
	 *  	P = (-b)
	 */
	@org.junit.Test
	public void test4() {
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        
        BoolExpr a = ctx.mkBoolConst("a");
        BoolExpr b = ctx.mkBoolConst("b");
        BoolExpr c = ctx.mkBoolConst("c");
        
        BoolExpr I = ctx.mkAnd(a, ctx.mkNot(b), ctx.mkNot(c));
        
        BoolExpr T1 = ctx.mkEq(a, toPrime(c,ctx));
        BoolExpr T2 = ctx.mkEq(b, toPrime(a,ctx));
        BoolExpr T3 = ctx.mkEq(c, toPrime(b,ctx));
        BoolExpr T = ctx.mkAnd(T1,T2,T3);
        
        Expr P = ctx.mkNot(b);
        
        check(I, T, P, ctx);
	}
	private static void check(Expr I, BoolExpr T, Expr P, Context ctx) {
		long start = System.currentTimeMillis();
		PDR mc = new PDR(I, T, P, ctx);
		for (Interpretation interp : mc.check()) {
			System.out.println(interp);
		}
		long stop = System.currentTimeMillis();
		System.out.println("Time: " + (stop - start) / 1000.0);
		mc.showFrames();
		System.out.println();
	}
	
	private BoolExpr toPrime(BoolExpr e, Context ctx){
		return ctx.mkBoolConst(e.getFuncDecl().getName().toString() + "\'");
	}
	
	
}

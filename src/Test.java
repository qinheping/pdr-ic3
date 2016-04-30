import static org.junit.Assert.*;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import com.microsoft.z3.*;

public class Test {

	/*	UNSAFE
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
        
        BoolExpr P = ctx.mkNot(ctx.mkAnd(a, b));
        System.out.println("Test1:");
        check(I,T, P, ctx);
	}
	
	/*	SAFE
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
        
        BoolExpr T1 = ctx.mkOr(ctx.mkNot(a), (BoolExpr)toPrime(c, ctx));
        BoolExpr T2 = ctx.mkOr(a, ctx.mkNot((BoolExpr)toPrime(c, ctx)));
        BoolExpr T3 = ctx.mkOr(b, ctx.mkNot((BoolExpr)toPrime(b, ctx)));
        BoolExpr T4 = ctx.mkOr(ctx.mkNot(a),ctx.mkNot(b), ctx.mkNot((BoolExpr)toPrime(a, ctx)));
        BoolExpr T5 = ctx.mkOr(ctx.mkNot(c),a,(BoolExpr) toPrime(a, ctx));
        BoolExpr T6 = ctx.mkOr(ctx.mkNot(c),b, (BoolExpr)toPrime(a, ctx));
        BoolExpr T = ctx.mkAnd(T1,T2,T3,T4,T5,T6);
        
        BoolExpr P = ctx.mkNot(ctx.mkAnd(a, b, c));
        System.out.println("Test2:");
        check(I,T, P, ctx);
	}
	
	/*
	 * 	UNSAFE
	 *  test3:
	 *  	I = (00000001)
	 *  	T : T(b_i) = b_{i-1} xor b_{i+1}
	 *  	P = -(00000000)
	 */
	@org.junit.Test
	public void test3() {
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        int length = 8;
        BoolExpr[] b = new BoolExpr[8];   
        
        BoolExpr I = ctx.mkTrue();
        for(int i = 0; i < 8; i ++){
        	b[i] = ctx.mkBoolConst("b"+i);
        	if(i == length-1)
        	I = ctx.mkAnd(I, b[i]);
        	else
        		I = ctx.mkAnd(I,ctx.mkNot(b[i]));
        }
        
        BoolExpr[] Targs = new BoolExpr[length];
        for(int i = 0; i < 8; i ++){
        	int pre = (i+9)%length;
        	int post = (i+1)%length;
        	Targs[i] = ctx.mkEq(toPrime(b[i],ctx), ctx.mkXor(b[post], b[pre]));
        }
        BoolExpr T = ctx.mkAnd(Targs);
        
        BoolExpr P = ctx.mkTrue();
        for(int i = 0; i < 8; i ++){
        	b[i] = ctx.mkBoolConst("b"+i);
        	P = ctx.mkAnd(P,ctx.mkNot(b[i]));
        }
        P = ctx.mkNot(P);
        
        System.out.println("Test3:");
        check(I, T, P, ctx);
	}
	
	/*
	 *  UNSAFE
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
        
        BoolExpr P = ctx.mkNot(b);
        System.out.println("Test4:");
        check(I, T, P, ctx);
	}
	
	/*
	 * 	SAFE
	 *  test5:
	 *  	I = (00000001)
	 *  	T : T(b_i) = b_{i-1} xor b_{i+1}
	 *  	P = -(10000000)
	 */
	@org.junit.Test
	public void test5() {
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        int length = 8;
        BoolExpr[] b = new BoolExpr[8];   
        
        BoolExpr I = ctx.mkTrue();
        for(int i = 0; i < 8; i ++){
        	b[i] = ctx.mkBoolConst("b"+i);
        	if(i == length-1)
        	I = ctx.mkAnd(I, b[i]);
        	else
        		I = ctx.mkAnd(I,ctx.mkNot(b[i]));
        }
        
        BoolExpr[] Targs = new BoolExpr[length];
        for(int i = 0; i < 8; i ++){
        	int pre = (i+9)%length;
        	int post = (i+1)%length;
        	Targs[i] = ctx.mkEq(toPrime(b[i],ctx), ctx.mkXor(b[post], b[pre]));
        }
        BoolExpr T = ctx.mkAnd(Targs);
        
        BoolExpr P = ctx.mkTrue();
        for(int i = 0; i < 8; i ++){
        	b[i] = ctx.mkBoolConst("b"+i);
        	if(i == 0)
        	P = ctx.mkAnd(P, b[i]);
        	else
        		P = ctx.mkAnd(P,ctx.mkNot(b[i]));
        }
        P = ctx.mkNot(P);
        
        System.out.println("Test5:");
        check(I, T, P, ctx);
	}
	
	/*
	 *  SAFE
	 *  test6:
	 *  	I = (00000001)
	 *  	T : T(I) = I + 2
	 *  	P = -(10000000)
	 */
	@org.junit.Test
	public void test6() {
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        int length = 8;
        BoolExpr[] b = new BoolExpr[length];   
        
        BoolExpr I = ctx.mkTrue();
        for(int i = 0; i < length; i ++){
        	b[i] = ctx.mkBoolConst("b"+i);
        	if(i == length-1)
        	I = ctx.mkAnd(I, b[i]);
        	else
        		I = ctx.mkAnd(I,ctx.mkNot(b[i]));
        }
        
    	int carry = 0;
        BoolExpr[] Targs = new BoolExpr[length]; 
        Targs[length - 1] = ctx.mkEq(toPrime(b[length - 1],ctx), b[length-1]);
        for(int i = length - 1; i >= 0; i--){
        	if(i != length - 1){
    			BoolExpr alltrue = ctx.mkTrue();
        		for(int j = i + 1; j < length - 1; j++){
        			alltrue = ctx.mkAnd(alltrue,b[j]);
        		}
        		Targs[i] = ctx.mkAnd(ctx.mkImplies(ctx.mkNot(alltrue), ctx.mkEq(toPrime(b[i],ctx), b[i])),
        							ctx.mkImplies(alltrue, ctx.mkEq(toPrime(b[i],ctx), ctx.mkNot(b[i]))));
        	}
        }
        BoolExpr T = ctx.mkAnd(Targs);
        
        BoolExpr P = ctx.mkTrue();
        for(int i = 0; i < length; i ++){
        	b[i] = ctx.mkBoolConst("b"+i);
        	if(i == 0)
        	P = ctx.mkAnd(P, b[i]);
        	else
        		P = ctx.mkAnd(P,ctx.mkNot(b[i]));
        }
        P = ctx.mkNot(P);
        
        System.out.println("Test6:");
        //check(I, T, P, ctx);
	}
	
	/*
	 *  UNSAFE
	 *  test7:
	 *  	I = (00000000)
	 *  	T : T(I) = I + 2
	 *  	P = -(10000000)
	 */
	@org.junit.Test
	public void test7() {
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        int length = 8;
        BoolExpr[] b = new BoolExpr[length];   
        
        BoolExpr I = ctx.mkTrue();
        for(int i = 0; i < length; i ++){
        	b[i] = ctx.mkBoolConst("b"+i);
        	//if(i == length-1)
        	//I = ctx.mkAnd(I, b[i]);
        	//else
        		I = ctx.mkAnd(I,ctx.mkNot(b[i]));
        }
        
    	int carry = 0;
        BoolExpr[] Targs = new BoolExpr[length]; 
        Targs[length - 1] = ctx.mkEq(toPrime(b[length - 1],ctx), b[length-1]);
        for(int i = length - 1; i >= 0; i--){
        	if(i != length - 1){
    			BoolExpr alltrue = ctx.mkTrue();
        		for(int j = i + 1; j < length - 1; j++){
        			alltrue = ctx.mkAnd(alltrue,b[j]);
        		}
        		Targs[i] = ctx.mkAnd(ctx.mkImplies(ctx.mkNot(alltrue), ctx.mkEq(toPrime(b[i],ctx), b[i])),
        							ctx.mkImplies(alltrue, ctx.mkEq(toPrime(b[i],ctx), ctx.mkNot(b[i]))));
        	}
        }
        BoolExpr T = ctx.mkAnd(Targs);
        
        BoolExpr P = ctx.mkTrue();
        for(int i = 0; i < length; i ++){
        	b[i] = ctx.mkBoolConst("b"+i);
        	if(i == 0)
        	P = ctx.mkAnd(P, b[i]);
        	else
        		P = ctx.mkAnd(P,ctx.mkNot(b[i]));
        }
        P = ctx.mkNot(P);

        System.out.println("Test7:");
        check(I, T, P, ctx);
	}
	
	/*
	 *  UNSAFE
	 *  test8:
	 *  	I = (1111111110)
	 *  	T : T(b_i) = b_{i-1} and b_{i-2}
	 *  	P = -(0000000000)
	 */
	@org.junit.Test
	public void test8() {
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        int length = 10;
        BoolExpr[] b = new BoolExpr[length];   
        
        BoolExpr I = ctx.mkTrue();
        for(int i = 0; i < length; i ++){
        	b[i] = ctx.mkBoolConst("b"+i);
        	if(i != length-1)
        	I = ctx.mkAnd(I, b[i]);
        	else
        		I = ctx.mkAnd(I,ctx.mkNot(b[i]));
        }
        
        BoolExpr[] Targs = new BoolExpr[length];
        for(int i = 0; i < length; i ++){
        	int pre = (i+9)%length;
        	int post = (i+10)%length;
        	Targs[i] = ctx.mkEq(toPrime(b[i],ctx), ctx.mkAnd(b[post], b[pre]));
        }
        BoolExpr T = ctx.mkAnd(Targs);
        
        BoolExpr P = ctx.mkTrue();
        for(int i = 0; i < length; i ++){
        	b[i] = ctx.mkBoolConst("b"+i);
        	P = ctx.mkAnd(P,ctx.mkNot(b[i]));
        }
        P = ctx.mkNot(P);
        System.out.println("Test8:");
        check(I, T, P, ctx);
	}
	
	private static void check(BoolExpr I, BoolExpr T, BoolExpr P, Context ctx) {
		long start = System.currentTimeMillis();
		PDR mc = new PDR(I, T, P, ctx);
		for (Interpretation interp : mc.check()) {
			System.out.println(interp);
		}
		long stop = System.currentTimeMillis();
		System.out.println("Time: " + (stop - start) / 1000.0);
		//mc.showFrames();
		System.out.println();
	}
	
	private Expr toPrime(Expr e, Context ctx){
		return ctx.mkConst(e.getFuncDecl().getName().toString() + "\'",e.getSort());
	}
	
	
}

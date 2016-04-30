import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import com.microsoft.z3.Expr;
import com.microsoft.z3.Symbol;


	// a interpretation is an (partial) assignment
	public class Interpretation{
		public final Map<Symbol, Boolean> map;
		public Interpretation(Map<Symbol, Boolean> map) {
			this.map = Collections.unmodifiableMap(map);
		}
		@Override
		public String toString() {
			String s = "[ ";
			for(Symbol e: map.keySet()){
				s += e + "->" + map.get(e) + " ";
			}
			return s + "]";
		}
		public Interpretation remove(Symbol key){
			Map<Symbol, Boolean> map = new HashMap<>(this.map);
			map.remove(key);
			return new Interpretation(map);
		}
	}
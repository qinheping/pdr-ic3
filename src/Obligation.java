//
public class Obligation implements Comparable<Obligation>{
		public final Cube s;
		public final int k;

		public Obligation(Cube s, int k) {
			this.s = s;
			this.k = k;
		}
		public int compareTo(Obligation other) {
			int r = Integer.compare(k, other.k);
			if (r != 0) {
				return r;
			}
			return s.toString().compareTo(other.s.toString());
		}
		@Override
		public boolean equals(Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (!(obj instanceof Obligation)) {
				return false;
			}
			Obligation other = (Obligation) obj;
			if (k != other.k) {
				return false;
			}
			if (s == null) {
				if (other.s != null) {
					return false;
				}
			} else if (!s.equals(other.s)) {
				return false;
			}
			return true;
		}
	}
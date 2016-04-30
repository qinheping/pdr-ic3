import java.util.List;


	
// a counter example is a list of interpretation such that we can reach negP from I step by step
public class Counterexample extends RuntimeException {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	public final List<Interpretation> cex;
	public Counterexample(List<Interpretation> cex) {
		this.cex = cex;
	}
}
	
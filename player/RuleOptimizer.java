import java.util.ArrayList;
import java.util.List;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlDistinct;
import org.ggp.base.util.gdl.grammar.GdlFunction;
import org.ggp.base.util.gdl.grammar.GdlLiteral;
import org.ggp.base.util.gdl.grammar.GdlPool;
import org.ggp.base.util.gdl.grammar.GdlRule;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.gdl.grammar.GdlTerm;

public class RuleOptimizer {

	private static void sanitizeDistinctHelper(Gdl gdl, List<Gdl> in, List<Gdl> out) {
		if (!(gdl instanceof GdlRule)) {
			out.add(gdl);
			return;
		}
		GdlRule rule = (GdlRule) gdl;
		for (GdlLiteral lit : rule.getBody()) {
			if (lit instanceof GdlDistinct) {
				GdlDistinct d = (GdlDistinct) lit;
				GdlTerm a = d.getArg1();
				GdlTerm b = d.getArg2();
				if (!(a instanceof GdlFunction) && !(b instanceof GdlFunction)) continue;
				if (!(a instanceof GdlFunction && b instanceof GdlFunction)) return;
				GdlSentence af = ((GdlFunction) a).toSentence();
				GdlSentence bf = ((GdlFunction) b).toSentence();
				if (!af.getName().equals(bf.getName())) return;
				if (af.arity() != bf.arity()) return;
				for (int i = 0; i < af.arity(); i++) {
					List<GdlLiteral> ruleBody = new ArrayList<>();
					for (GdlLiteral newLit : rule.getBody()) {
						if (newLit != lit) ruleBody.add(newLit);
						else ruleBody.add(GdlPool.getDistinct(af.get(i), bf.get(i)));
					}
					GdlRule newRule = GdlPool.getRule(rule.getHead(), ruleBody);
					Log.println("new rule: " + newRule);
					in.add(newRule);
				}
				return;
			}
		}
		for (GdlLiteral lit : rule.getBody()) {
			if (lit instanceof GdlDistinct) {
				Log.println("distinct rule added: " + rule);
				break;
			}
		}
		out.add(rule);
	}

	public static List<Gdl> sanitizeDistinct(List<Gdl> description) {
		List<Gdl> out = new ArrayList<>();
		for (int i = 0; i < description.size(); i++) {
			sanitizeDistinctHelper(description.get(i), description, out);
		}
		return out;
	}
}

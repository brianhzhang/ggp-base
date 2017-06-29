import java.awt.Font;
import java.awt.LayoutManager;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JButton;
import javax.swing.JLabel;

import org.ggp.base.apps.player.config.ConfigPanel;

@SuppressWarnings("serial")
public class Config extends ConfigPanel {

	JLabel current;

	private void addMethod(MyPlayer m, String name, int method) {
		JButton button = new JButton(name);
		button.setFont(new Font("Verdana", Font.PLAIN, 18));
		button.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				m.method = method;
				current.setText("Current Strategy: " + name);
			}
		});
		add(button);
	}

	public Config(LayoutManager layout, final MyPlayer m) {
		super(layout);

		current = new JLabel("Current Strategy: Machine Learning", (int) CENTER_ALIGNMENT);
		current.setFont(new Font("Verdana", Font.BOLD, 24));

		add(current);
		addMethod(m, "Legal", MyPlayer.LEGAL);
		addMethod(m, "Random", MyPlayer.RANDOM);
		addMethod(m, "Alpha-Beta", MyPlayer.ALPHABETA);
		addMethod(m, "Heuristic", MyPlayer.HEURISTIC);
		addMethod(m, "Monte Carlo", MyPlayer.MONTECARLO);
		addMethod(m, "MCTS", MyPlayer.MCTS);
		addMethod(m, "Experimental", MyPlayer.EXPERIMENTAL);
		addMethod(m, "Machine Learning", MyPlayer.ML);
	}

}

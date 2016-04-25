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

	public Config(LayoutManager layout, final MyPlayer m) {
		super(layout);

		current = new JLabel("Current Strategy: ", (int) CENTER_ALIGNMENT);
		current.setFont(new Font("Verdana", Font.BOLD, 25));

		JButton legalButton = new JButton("Legal");
		legalButton.setFont(new Font("Verdana", Font.PLAIN, 25));
		JButton randomButton = new JButton("Random");
		randomButton.setFont(new Font("Verdana", Font.PLAIN, 25));
		JButton abButton = new JButton("Alpha-Beta");
		abButton.setFont(new Font("Verdana", Font.PLAIN, 25));
		JButton hButton = new JButton("Heuristic");
		hButton.setFont(new Font("Verdana", Font.PLAIN, 25));
		JButton mcButton = new JButton("Monte Carlo");
		mcButton.setFont(new Font("Verdana", Font.PLAIN, 25));

		legalButton.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e){
				m.method = MyPlayer.LEGAL;
				current.setText("Current Strategy: Legal");
			}
		});
		randomButton.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e){
				m.method = MyPlayer.RANDOM;
				current.setText("Current Strategy: Random");
			}
		});
		abButton.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e){
				m.method = MyPlayer.ALPHABETA;
				current.setText("Current Strategy: Alpha-Beta");
			}
		});
		hButton.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e){
				m.method = MyPlayer.HEURISTIC;
				current.setText("Current Strategy: Heuristic");
			}
		});
		mcButton.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e){
				m.method = MyPlayer.MONTECARLO;
				current.setText("Current Strategy: Monte Carlo");
			}
		});

		this.add(current);
		this.add(legalButton);
		this.add(randomButton);
		this.add(abButton);
		this.add(hButton);
		this.add(mcButton);
	}

}

//@author Igor Lesik 2013
//
import java.sql.*;

import javax.swing.JPanel;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JTabbedPane;
import javax.swing.BorderFactory;
import javax.swing.border.Border;
import javax.swing.BoxLayout;
import javax.swing.Box;
import java.awt.*;

public class POMainPanel extends JPanel
{
    java.sql.Connection _sql;

    JFrame _frame;
    JLabel _statusBar;

    /** Creates the GUI shown inside the frame's content pane. */
    public POMainPanel(JFrame frame, Connection sql)
    {
        super(new BorderLayout());
        this._frame = frame;

        this._sql = sql;

        //Create the components.
        JPanel peoplePanel = createPeoplePanel();
        //JPanel featurePanel = createFeatureDialogBox();
        //JPanel iconPanel = createIconDialogBox();
        _statusBar = new JLabel("Welcome to OpenPO!",
                           JLabel.CENTER);

        //Lay them out.
        Border padding = BorderFactory.createEmptyBorder(20,20,5,20);
        peoplePanel.setBorder(padding);
        //featurePanel.setBorder(padding);
        //iconPanel.setBorder(padding);

        JTabbedPane tabbedPane = new JTabbedPane();
        tabbedPane.addTab("People", null,
                          peoplePanel,
                          "People that make Purchase Requisitions"); //tooltip text
        //tabbedPane.addTab("More Dialogs", null,
        //                  featurePanel,
        //                  moreDialogDesc); //tooltip text
        //tabbedPane.addTab("Dialog Icons", null,
        //                  iconPanel,
        //                  iconDesc); //tooltip text

        add(tabbedPane, BorderLayout.CENTER);
        add(_statusBar, BorderLayout.PAGE_END);
        _statusBar.setBorder(BorderFactory.createEmptyBorder(10,10,10,10));
    }

    private JPanel createPeoplePanel()
    {
        JPanel panel = new POPeoplePanel(_sql);

        return panel;
    }
}

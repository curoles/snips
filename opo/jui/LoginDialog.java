// @author Igor Lesik 2013
//

import javax.swing.JOptionPane;
import javax.swing.JDialog;
import javax.swing.JTextField;
import javax.swing.JPasswordField;
import java.beans.*; //property change stuff
import java.awt.*;
import java.awt.event.*;

import java.sql.*;
import java.util.Properties;

class LoginDialog extends JDialog implements ActionListener, PropertyChangeListener
{
    private Connection _mysqlConnection = null;

    private JTextField _txtFldHost;
    private JTextField _txtFldUser;
    private JTextField _txtFldPassw;

    private JOptionPane _optionPane;

    private String _btnStringLogin = "Login";
    private String _btnStringCancel = "Cancel";

    public Connection getMySQLConnection() {
        return _mysqlConnection;
    }

    /** Creates the dialog. */
    public LoginDialog(Frame aFrame/*, String aWord, DialogDemo parent*/)
        throws ClassNotFoundException
    {
        super(aFrame, true);

        // The JDBC Connector Class.
        String dbClassName = "com.mysql.jdbc.Driver";

        // Class.forName(xxx) loads the jdbc classes and
        // creates a drivermanager class factory
        Class.forName(dbClassName);
        //throws ClassNotFoundException


        setTitle("Login to MySQL");

        _txtFldHost = new JTextField(10);
        _txtFldHost.setText("127.0.0.1");
        _txtFldUser = new JTextField(10);
        _txtFldPassw = new JPasswordField(10);

        //Create an array of the text and components to be displayed.
        String msgStringHost = "MySQL Server Host:";
        String msgStringUser = "MySQL User:";
        String msgStringPassw = "Password:";

        Object[] ui_components_array = {
            msgStringHost, _txtFldHost,
            msgStringUser, _txtFldUser,
            msgStringPassw, _txtFldPassw,
        };

        //Create an array specifying the number of dialog buttons
        //and their text.
        Object[] options = {_btnStringLogin, _btnStringCancel};

        //Create the JOptionPane.
        _optionPane = new JOptionPane(ui_components_array,
                                    JOptionPane.QUESTION_MESSAGE,
                                    JOptionPane.YES_NO_OPTION,
                                    null,
                                    options,
                                    options[0]);

        //Make this dialog display it.
        setContentPane(_optionPane);

        //Handle window closing correctly.
        setDefaultCloseOperation(DO_NOTHING_ON_CLOSE);

        addWindowListener(new WindowAdapter()
        {
            public void windowClosing(WindowEvent we) {
                /*
                 * Instead of directly closing the window,
                 * we're going to change the JOptionPane's
                 * value property.
                 */
                 _optionPane.setValue(new Integer(JOptionPane.CLOSED_OPTION));
            }
        });

        //Ensure the text field always gets the first focus.
        addComponentListener(new ComponentAdapter() {
            public void componentShown(ComponentEvent ce) {
                _txtFldHost.requestFocusInWindow();
            }
        });

        //Register an event handler that puts the text into the option pane.
        _txtFldHost.addActionListener(this);
        _txtFldUser.addActionListener(this);
        _txtFldPassw.addActionListener(this);

        //Register an event handler that reacts to option pane state changes.
        _optionPane.addPropertyChangeListener(this);
    }

    /** This method handles events for the text field. */
    public void actionPerformed(ActionEvent e) {
        _optionPane.setValue(_btnStringLogin);
    }

    /** This method reacts to state changes in the option pane. */
    public void propertyChange(PropertyChangeEvent e)
    {
        String prop = e.getPropertyName();

        if (isVisible()
         && (e.getSource() == _optionPane)
         && (JOptionPane.VALUE_PROPERTY.equals(prop) ||
             JOptionPane.INPUT_VALUE_PROPERTY.equals(prop)))
        {
            Object value = _optionPane.getValue();

            if (value == JOptionPane.UNINITIALIZED_VALUE) {
                //ignore reset
                return;
            }

            //Reset the JOptionPane's value.
            //If you don't do this, then if the user
            //presses the same button next time, no
            //property change event will be fired.
            _optionPane.setValue(
                    JOptionPane.UNINITIALIZED_VALUE);

            if (_btnStringLogin.equals(value))
            {
                try
                {
                    _mysqlConnection = connectToMySQL(
                        _txtFldHost.getText(),
                        _txtFldUser.getText(),
                        _txtFldPassw.getText()
                    );
                }
                catch (SQLException ex)
                {

                }

                if (_mysqlConnection == null)
                {
                    JOptionPane.showMessageDialog(
                        LoginDialog.this,
                        "Sorry, could not connect to MySQL PO DB\nTry again",
                        "ERROR: can't connect to MySQL",
                        JOptionPane.ERROR_MESSAGE
                    );
                    _txtFldHost.requestFocusInWindow();
                }
                else
                {
                    clearAndHide();
                }

            }
            else //user closed dialog or clicked cancel
            {
                clearAndHide();
            }
        }
    }

    /** This method clears the dialog and hides it. */
    public void clearAndHide()
    {
        setVisible(false);
    }

    public Connection connectToMySQL(String host, String user, String passwd)
        throws SQLException
    {
        // Properties for user and password.
        Properties p = new Properties();
        p.put("user", user);
        p.put("password", passwd);

        String CONNECTION = "jdbc:mysql://"+host+"/podb";

        //System.out.println("connecting to "+CONNECTION+" ...");

        // Now try to connect
        Connection conn = DriverManager.getConnection(CONNECTION,p);

        // Print all warnings
        for (SQLWarning warn = conn.getWarnings(); warn != null; warn = warn.getNextWarning())
        {
            System.out.println( "SQL Warning:" );
            System.out.println( "  State  : " + warn.getSQLState()  );
            System.out.println( "  Message: " + warn.getMessage()   );
            System.out.println( "  Error  : " + warn.getErrorCode() );
        }

        return conn;
    }
}


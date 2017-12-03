//@author Igor Lesik 2013
//
import java.sql.*;
import java.net.URL;
import java.awt.Toolkit;
import java.awt.Image;

//import java.util.Properties;
//import javax.swing.JOptionPane;
import javax.swing.JFrame;
//import java.awt.*;

public class POApp
{

    public static void main(String[] args)
        throws ClassNotFoundException, SQLException
    {
        final Connection sql = openLoginDialog();

        if (sql == null)
        {
            System.out.println("NO MySQL CONNECTION, EXIT!");
        }
        else
        {
            System.out.println("Connection to MySQL DB established!");

            //Schedule a job for the event-dispatching thread:
            //creating and showing this application's GUI.
            javax.swing.SwingUtilities.invokeLater(new Runnable() {
                public void run() {
                    createAndShowGUI(sql);
                }
            });

            Runtime.getRuntime().addShutdownHook(new Thread(new Runnable() {
                public void run() {
                    // Do here what we need when the application is stopping
                     try {sql.close();}catch(Exception e){}
                    System.out.println("SQL connection closed");
                }
            }));
        }

    }

    private static Connection openLoginDialog() throws ClassNotFoundException
    {
        LoginDialog loginDialog = new LoginDialog(null);
        loginDialog.pack();
        loginDialog.setResizable(false);
        loginDialog.setLocationRelativeTo(null);
        loginDialog.setVisible(true);
        Connection sql = loginDialog.getMySQLConnection();
        loginDialog.dispose();
        return sql;
    }

    /**
     * Create the GUI and show it.  For thread safety,
     * this method should be invoked from the
     * event-dispatching thread.
     */
    private static void createAndShowGUI(Connection sql)
    {
        //Create and set up the window.
        JFrame frame = new JFrame("OpenPO");
        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        setAppIcon(frame);

        //Create and set up the content pane.
        POMainPanel newContentPane = new POMainPanel(frame, sql);
        newContentPane.setOpaque(true); //content panes must be opaque
        frame.setContentPane(newContentPane);

        //Display the window.
        frame.pack();
        frame.setLocationRelativeTo(null);
        frame.setVisible(true);
    }

    private static void setAppIcon(JFrame frame)
    {
        URL url = ClassLoader.getSystemResource("images/opo.png");
        Toolkit kit = Toolkit.getDefaultToolkit();
        Image img = kit.createImage(url);
        frame.setIconImage(img);
    }
}

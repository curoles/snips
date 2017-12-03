//@author Igor Lesik 2013
//
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JToolBar;
import javax.swing.JLabel;
import javax.swing.JButton;
import javax.swing.JTable;
import javax.swing.JTextField;
import javax.swing.table.TableModel;
import javax.swing.table.AbstractTableModel;
import javax.swing.BorderFactory;
import javax.swing.border.Border;
import javax.swing.BoxLayout;
import javax.swing.Box;
import java.awt.*;
import java.awt.event.*;

import java.sql.*;

import java.util.Vector;

class PeopleTableModel extends AbstractTableModel
{
    java.sql.Connection _sql;

    private String[] _columnNames = {
        "Id",
        "First Name",
        "Last Name",
        "Current",
        "Phone",
        "Email"
    };

    private Vector< Object[] > _data;

    public PeopleTableModel(Connection sql)
    {
        _sql = sql;

        _data = new Vector<Object[]>(10, 10);
        getDataFromDB();//TODO when visible first time
    }

    private void getDataFromDB()
    {
        _data.clear();

        Statement stmt = null;
        String query =
            "SELECT * " +
            "FROM person";

        try
        {
            stmt = _sql.createStatement();
            ResultSet rs = stmt.executeQuery(query);
            while (rs.next())
            {
                int id = rs.getInt("id");
                String firstName = rs.getString("first_name");
                String lastName = rs.getString("last_name");
                Boolean current = new Boolean(rs.getString("current").equals("YES"));
                String phone = rs.getString("phone");
                String email = rs.getString("email");

                Object[] row = {new Integer(id), firstName, lastName,
                    current/*new Boolean(false)*/, phone, email};

                _data.add(row);
            }
        } catch (SQLException e ) {
            //JDBCTutorialUtilities.printSQLException(e);
        } finally {
            if (stmt != null) { try {stmt.close();}catch(SQLException e){}finally{} }
        }

        //if (stmt != null) { try {stmt.close();}catch(SQLException e){}finally{} }

    }

    public int getColumnCount() {
        return _columnNames.length;
    }

    public int getRowCount() {
        return _data.size();
    }

    public String getColumnName(int col) {
        return _columnNames[col];
    }

    public Object getValueAt(int row, int col) {
        Object val = null;
        try {val = _data.get(row)[col];}
        catch (ArrayIndexOutOfBoundsException e) {}
        return val;
    }

    /*
     * JTable uses this method to determine the default renderer/
     * editor for each cell.  If we didn't implement this method,
     * then the last column would contain text ("true"/"false"),
     * rather than a check box.
     */
    public Class getColumnClass(int c) {
        return getValueAt(0, c).getClass();
    }

    /*
     * Don't need to implement this method unless your table's
     * editable.
     */
    public boolean isCellEditable(int row, int col) {
        //Note that the data/cell address is constant,
        //no matter where the cell appears onscreen.
        if (col < 2) {
            return false;
        } else {
            return true;
        }
    }

    /*
     * Don't need to implement this method unless your table's
     * data can change.
     */
    public void setValueAt(Object value, int row, int col)
    {
        /*if (DEBUG) {
            System.out.println("Setting value at " + row + "," + col
                               + " to " + value
                               + " (an instance of "
                               + value.getClass() + ")");
        }*/

        //_data.elemntAt(row)[col] = value;
        fireTableCellUpdated(row, col);

    }

}

class NewPersonTableModel extends AbstractTableModel
{
    java.sql.Connection _sql;

    private String[] _columnNames = {
        "Id",
        "First Name",
        "Last Name",
        "Current",
        "Phone",
        "Email"
    };

    private Object[] _data;

    public NewPersonTableModel(Connection sql)
    {
        _sql = sql;

        _data = new Object[]{"-", "First", "Last", new Boolean(true), "", "-@-"};
    }

    public int getColumnCount() {
        return _columnNames.length;
    }

    public int getRowCount() {
        return 1;
    }

    public String getColumnName(int col) {
        return _columnNames[col];
    }

    public Object getValueAt(int row, int col) {
        Object val = null;
        try {val = _data[col];}
        catch (ArrayIndexOutOfBoundsException e) {}
        return val;
    }

    /*
     * JTable uses this method to determine the default renderer/
     * editor for each cell.
     *
     */
    public Class getColumnClass(int c) {
        return getValueAt(0, c).getClass();
    }

    public boolean isCellEditable(int row, int col) {
        //Note that the data/cell address is constant,
        //no matter where the cell appears onscreen.
        if (col < 1) {
            return false;
        } else {
            return true;
        }
    }

    public void setValueAt(Object value, int row, int col)
    {
        _data[col] = value;
        fireTableCellUpdated(row, col);
    }

    // end of TableModel interface

    public void makeNewRecord()
    {
        String query = "INSERT INTO person(first_name, last_name, phone, email) VALUES("+
            "\'"+_data[1].toString()+"\',\'"+_data[2].toString()+"\',\'"+
            _data[4].toString()+"\',\'"+_data[5].toString()+"\')";

        Statement stmt = null;

        try
        {
            stmt = _sql.createStatement();
            stmt.executeUpdate(query);
        } catch (SQLException e ) {
            System.out.println("SQLException for query:"+query);
            System.out.println("SQLException:"+e.getMessage());
            //JDBCTutorialUtilities.printSQLException(e);
        } finally {
            if (stmt != null) { try {stmt.close();}catch(SQLException e){}finally{} }
        }

    }
}

class QueryPeoplePanel extends JPanel //implements ActionListener
{
    TableModel _pplTableModel;
    JTable     _pplTable;

    public QueryPeoplePanel(Connection sql)
    {
        super(new BorderLayout());

        _pplTableModel = new PeopleTableModel(sql);
        _pplTable = new JTable(_pplTableModel);

        JScrollPane pplScrollPane = new JScrollPane(_pplTable);
        _pplTable.setFillsViewportHeight(true);

        JToolBar toolBar = new JToolBar();
        toolBar.setFloatable(false);
        toolBar.setRollover(true);
        JButton buttonQuery = new JButton("QUERY");
        //button.setActionCommand(actionCommand);
        //button.setToolTipText(toolTipText);
        //button.addActionListener(this);
        toolBar.add(buttonQuery);
        JTextField queryTextField = new JTextField("SELECT * FROM person");
        toolBar.add(queryTextField);

        add(toolBar, BorderLayout.PAGE_START);
        add(pplScrollPane, BorderLayout.CENTER);
    }
}

class NewPersonPanel extends JPanel implements ActionListener
{
    NewPersonTableModel _newPersonTableModel;
    JTable     _newPersonTable;

    public NewPersonPanel(Connection sql)
    {
        super(new BorderLayout());

        _newPersonTableModel = new NewPersonTableModel(sql);
        _newPersonTable = new JTable(_newPersonTableModel);

        JScrollPane newPersonScrollPane = new JScrollPane(_newPersonTable);
        _newPersonTable.setFillsViewportHeight(true);

        JToolBar toolBar = new JToolBar();
        toolBar.setFloatable(false);
        toolBar.setRollover(true);
        JButton buttonNewPerson = new JButton("NEW");
        buttonNewPerson.setActionCommand("NEW");
        buttonNewPerson.setToolTipText("Create record about a person");
        buttonNewPerson.addActionListener(this);
        toolBar.add(buttonNewPerson);

        add(toolBar, BorderLayout.PAGE_START);
        add(newPersonScrollPane, BorderLayout.CENTER);
    }

    public void actionPerformed(ActionEvent event)
    {
        if(event.getActionCommand().equals("NEW"))
        {
            _newPersonTableModel.makeNewRecord();
        }
    }
}

public class POPeoplePanel extends JPanel
{
    QueryPeoplePanel _queryPanel;
    NewPersonPanel _newPersonPanel;


    public POPeoplePanel(Connection sql)
    {
        super(new BorderLayout());

        _queryPanel = new QueryPeoplePanel(sql);

        _newPersonPanel = new NewPersonPanel(sql);

        //Create a split pane with the two scroll panes in it.
        JSplitPane splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT,
            _newPersonPanel, _queryPanel);
        splitPane.setOneTouchExpandable(true);
        splitPane.setDividerLocation(80);

        //Provide minimum sizes for the two components in the split pane
        Dimension minimumSize = new Dimension(200, 80);
        _queryPanel.setMinimumSize(minimumSize);
        _newPersonPanel.setMinimumSize(minimumSize);

        //Provide a preferred size for the split pane.
        splitPane.setPreferredSize(new Dimension(800, 800));

        this.add(splitPane/*scrollPane*/, BorderLayout.PAGE_START);

    }

}

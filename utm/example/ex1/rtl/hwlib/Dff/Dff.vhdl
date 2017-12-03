library ieee;
use ieee.std_logic_1164.all;

entity Dff is
    generic (WIDTH: integer);
    port (clk:   in  std_logic;
          inp:   in  std_logic_vector(width-1 downto 0);
          outp:  out std_logic_vector(width-1 downto 0)
    );
end Dff;

architecture Rtl of Dff is
begin
    process(clk) 
    begin
        if rising_edge(clk) then
            outp <= inp;
        end if;
    end process;
end;

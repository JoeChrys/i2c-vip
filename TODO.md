## Questions

##### General

- [ ] 1. Should I make a modifiable clock for different speed modes?

##### Data Item

- [ ] 1. How to create a new global type (enum) for item type?

##### Driver

- [ ] 1. How will the driver generate clock?
    - Should I base it on system_clock signal?
    - Clock period should be ``LOW-HIGH-LOW`` instead of ``HIGH-LOW``

        | value | time |
        |---|---|
        | LOW | ${(1-duty) \over 2} \cdot period$ |
        | HIGH | $duty \cdot period$ |
        | LOW | ${(1-duty) \over 2} \cdot period$ |

- [ ] 2. How to drive SDA and SCL in correct order?
    - Should I use<br> ``wait(scl == 0); sda = data;`` ?

##### UVM
- [ ] 1. When trying to test multiple contollers (masters), I should use a different env with 2 master agents?

---

## TODO:

- [x] Interface
    - [x] Pullup behavior when `1'bZ`
    - [x] Basic assertions for `1'bX`
    - [ ] Assertion for pullup behavior
- [ ] Data item
    - [ ] Member variables
    - [x] Constraints
    - [ ] Register variables to factory
- [ ] Driver
    - [ ] Bit driving (setting SDA and SCL in the correct order prefferably without using delays)
    - [ ] Bit check after sending (for  [UVM 2.](#uvm))


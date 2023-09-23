##### 11/09
- Changed item structure
    - start, stop now (oprionally) surround data in an item
    - data is now a dynamic array comprised of bytes

- Changed monitor to adapt to new item structure

##### 13/09
- Changed master driver to adapt to new item structure

##### 14/09
- Added assertions to interface

##### 18/09
- Decided with Nick to change the item structure a bit, now the item.data is 
a single byte instead of a dynamic byte array
- Minor changes to adapt, e.g. added item.transfer_failed flag

##### 19/09
- Adapted Master driver to new structure, cleaned up code

##### 20/09
- Rewritten Monitor to adapt to new structure

##### 21/09
- Implemented master sequence
- Implemented slave sequence

##### 22/09
- Finished slave driver
- Added clock stretching at data bits
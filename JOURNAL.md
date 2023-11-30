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

##### 24/09
- Minor changes to drivers

##### 27/09
- Simplified slave driver logic
- Added fatal exceptions, removed error handling logic

##### 21/11 Long time no see
- Drivers working as expected
- Initial work on sequences is done
- Trying to find pieces of code to refine for new sequence logic

##### 22/11
- Studied SVA, SVAUnit
- Minor changes to sequences, scrapped stop_on_ack/fail for now

##### 23/11
- SVA studying, found 2 differnt approaches (see NOTES)
- unscrapped stop_on_ack/fail :P

##### 27/11 !!
- Sequences are running perfectly

##### 28/11
- Added most of reserved address sequences (MASTER)
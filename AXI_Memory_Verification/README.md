# AXI Memory Verification
---------------------------------------

*Advanced eXtensible Interface (AXI) is an on-chip communication bus protocol which is part of the Advanced Microcontroller Bus Architecture specification (AMBA).Here we are using an AXI memory as DUT*<br>
<br>

## Tasks
1. AXI protocol understanding<br>
   [AMBA AXI](https://www.google.com/url?sa=t&rct=j&q=&esrc=s&source=web&cd=&ved=2ahUKEwiQzb33nP2CAxWMRmcHHRVGCSYQFnoECBcQAQ&url=https%3A%2F%2Fdocumentation-service.arm.com%2Fstatic%2F5f915920f86e16515cdc3342%3Ftoken%3D&usg=AOvVaw2512gw412xiXzIkXoe8ZSC&opi=89978449) <br>
3. Obtain synthesizable design<br>
   Here we disgned an AXI memory of 128B. The design coded as per the axi protocol specification with few assumption to reduce the complexity of design.<br>
   * Don't have atomic access
   * Don't have low power interface
   * Don't support interleaving transactions
   * Don't have cache and protection unit support
   * Only have incrementing address burst
   
4. List of properties to be covered<br>
   Added the basic properties to be covered as per the protocol specification.
5. Assumptions and Assertions<br>
   Assumptions and assertions are included as per the user [guide for the AMBA AXI3](https://www.google.com/url?sa=t&rct=j&q=&esrc=s&source=web&cd=&ved=2ahUKEwin4KmyqbeDAxVFwjgGHX8yAx8QFnoECBQQAQ&url=https%3A%2F%2Fdocumentation-service.arm.com%2Fstatic%2F5fa14378b1a7c5445f290251%3Ftoken%3D&usg=AOvVaw2_zmlHYZiD0r3Q-aTAe6IX&opi=89978449) protocol.The prperties of master can be included as assumptions and the properties of slave can be included as assertions. Also other properties which is specific to our design also added.
6. Running and debugging<br>
   It is better to run step by step to debug easly.

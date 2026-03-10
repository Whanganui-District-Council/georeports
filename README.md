# GeoReports

![GeoReports](georeports_logo.svg)

GeoReports is a java servlet web application that provides end users with a powerful yet easy to use tool for creating a geographically rich PDF Report containing a series of predefined pages relating to a location of interest. 

An administrator pre-defines one or more GeoReports config files (XML), each defining how a single PDF Report will be constructed.  

A single GeoReports config file contains all the logic required to produce a PDF Report on almost any subject matter.

Examples of subject matter suitable for a GeoReports config file:
* Property Report
* Hazards Report
* LIM (New Zealand Land Information Memorandum)

Each page can contain combinations of maps and/or data derived from local data sources or via web services.

One or more Templates (QGIS QPT Layout Temlates) referenced by the config file define the page layouts required throughout the PDF Report.

Third party PDF documents can be inserted at any point either as defined pages, page ranges or an entire PDF document.

![Application Flow](georeports_application_flow.png)

# GeoReports Administrator Manual

[GeoReports Administrator Manual](https://github.com/Whanganui-District-Council/georeports-documentation-admin)


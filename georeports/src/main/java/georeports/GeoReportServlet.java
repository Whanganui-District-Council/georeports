package georeports;


import com.lowagie.text.*;
import com.lowagie.text.Image;
import com.lowagie.text.Rectangle;
import com.lowagie.text.pdf.*;
import com.lowagie.text.Font;

import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.xpath.*;

import java.awt.*;
import java.awt.geom.Point2D;
import java.io.*;
import java.net.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.time.ZoneId;
import java.time.ZonedDateTime;
import java.time.format.DateTimeFormatter;
import java.util.*;
import java.util.function.Predicate;
import java.util.regex.PatternSyntaxException;

import org.gdal.ogr.*;
import org.gdal.gdal.*;
import org.gdal.osr.*;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import org.slf4j.MDC;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import java.sql.ResultSet;
import java.sql.ResultSetMetaData;
import java.sql.SQLException;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.Statement;

import static com.lowagie.text.Utilities.millimetersToPoints;
import static com.lowagie.text.pdf.PdfContentByte.*;
import static java.lang.Math.abs;
import static java.lang.Math.round;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.stream.Collectors;


import java.util.concurrent.*;
import java.util.stream.Stream;

import org.apache.hc.core5.net.URIBuilder;




@WebServlet(urlPatterns = "/georeport/*", asyncSupported = true)
public class GeoReportServlet extends HttpServlet {

    // Initialize the Logger
    private static final Logger logger = LoggerFactory.getLogger(GeoReportServlet.class);
    private ExecutorService executor;
    private ScheduledExecutorService janitor;
    private final Map<String, PdfTask> mainTasks = new ConcurrentHashMap<>();
    private final Map<String, PdfTask> subTasks = new ConcurrentHashMap<>();
    private static final int MAX_RECURSION_DEPTH = 3;

    // configuration file variables
    private final String configPath = System.getenv("CONFIGURATION_PATH");
    private final String configFilePath = configPath + "config.properties";
    private final String dbConfigFilePath = configPath + "db_config.properties";


    // Required params
    String report;
    String featKey;

    // Optional Params
    String dataKey;
    String refKey;
    String scaleRaw;
    String s_epsgRaw;
    String t_epsgRaw;
    String xRaw;
    String yRaw;

    double p = 0;

    int textAlignment = 0; //default to left aligned
    float LabelPositionX = 0;
    float LabelPositionY = 0;
    float LabelWidth = 0;
    float LabelHeight = 0;

    // set default fonts
    Font titleFont = FontFactory.getFont(FontFactory.HELVETICA_BOLD, 12, Color.BLACK);
    Font descriptionFont = FontFactory.getFont(FontFactory.HELVETICA, 10, Color.BLACK);
    Font headerFont = FontFactory.getFont(FontFactory.HELVETICA_BOLD, 10, Color.BLACK);
    Font cellFont = FontFactory.getFont(FontFactory.HELVETICA, 10, Color.BLACK);

    // set default background colors
    Color titleColor = new Color(255, 255, 255,0);
    Color descriptionColor = new Color(255, 255, 255,0);
    //Color headerColor = new Color(255, 255, 255,255);
    Color headerColor = Color.LIGHT_GRAY;
    Color cellColor = new Color(255, 255, 255,255);
    Color alternateCellColor = new Color(245, 245, 245,255);

    // set default border colors
    Color titleBorderColor = new Color(0, 0, 0,0);
    Color descriptionBorderColor = new Color(0, 0, 0,0);
    Color headerBorderColor = new Color(0, 0, 0,255);
    Color cellBorderColor = new Color(0, 0, 0,255);
    Color alternateCellBorderColor = new Color(0, 0, 0,255);

    // set default border width
    float titleBorderWidth = 0.1f;
    float descriptionBorderWidth = 0.1f;
    float headerBorderWidth = 0.1f;
    float cellBorderWidth = 0.1f;
    float alternateCellBorderWidth = 0.1f;

    // Set default Neat Scale variable for scale calculations
    String MapImageNeatScale = "1";

    String MapImageX = "0";
    String MapImageY = "0";

    String MapImageWidth = "0";
    String MapImageHeight = "0";




    // Task state container
    private static class PdfTask {
        String reportType;
        String featureKey;
        String databaseKey;
        String referenceKey;
        String scaleRawValue;
        String s_epsgRawValue;
        String t_epsgRawValue;
        String xRawValue;
        String yRawValue;
        String error;
        volatile int progress = 0;
        volatile boolean isDone = false;
        Path tempFile;
        Future<?> future;

        PdfTask(String reportType, String featureKey, String databaseKey, String referenceKey,String scaleRawValue, String s_epsgRawValue, String t_epsgRawValue, String xRawValue, String yRawValue) {
            this.reportType = reportType;
            this.featureKey = featureKey;
            this.databaseKey = databaseKey;
            this.referenceKey = referenceKey;
            this.scaleRawValue = scaleRawValue;
            this.s_epsgRawValue = s_epsgRawValue;
            this.t_epsgRawValue = t_epsgRawValue;
            this.xRawValue = xRawValue;
            this.yRawValue = yRawValue;
        }
    }

    @Override
    public void init() {
        logger.info("Initializing GeoReports...");

        Properties initConfigs = new Properties();
        try {
            initConfigs.load(new FileInputStream(configFilePath));

            // Limit concurrent PDF generations to protect CPU/RAM
            executor = Executors.newFixedThreadPool(Integer.parseInt(initConfigs.getProperty("init.executorThreadPoolSize")));

            // Cleanup abandoned files
            janitor = Executors.newSingleThreadScheduledExecutor();
            janitor.scheduleAtFixedRate(this::cleanupAbandonedFiles, Integer.parseInt(initConfigs.getProperty("init.janitorCleanupDelayMinutes")), Integer.parseInt(initConfigs.getProperty("init.janitorCleanupPeriodMinutes")), TimeUnit.MINUTES);
        } catch (IOException e) {
            logger.info("Unable to initialise GeoReports.");
            throw new RuntimeException(e);
        }
        logger.info("GeoReports Initialized.");
    }

    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) throws IOException {
        String path = req.getPathInfo();

        if (path == null || path.equals("/")) {
            showUi(req, resp);
        } else if (path.equals("/direct")) {
            // Capture parameters from the URL: ?report=...&featkey=...
            handleDirectStream(req, resp);
        } else if (path.equals("/progress")) {
            // Capture parameters from the URL: ?report=...&featkey=...
            // displays progress bar then redirects to download
            handleProgressStream(req, resp);
        } else if (path.equals("/download")) {
            handleDownload(req, resp);
        } else {
            resp.sendError(HttpServletResponse.SC_NOT_FOUND);
        }
    }

    private void handleDirectStream(HttpServletRequest req, HttpServletResponse resp) throws IOException {
        String sessionId = req.getSession().getId();

        getURLParameters(req);

        if (dataKey == null){ dataKey = "";}
        if (refKey == null){ refKey = "";}
        if (scaleRaw == null){ scaleRaw = "";}
        if (s_epsgRaw == null){ s_epsgRaw = "";}
        if (t_epsgRaw == null){ t_epsgRaw = "";}
        if (xRaw == null){ xRaw = "";}
        if (yRaw == null){ yRaw = "";}

        MDC.put("sessionId", sessionId);

        logger.info("New direct request: Session={}, Report={}, FeatKey={}", sessionId, report, featKey);

        PdfTask task = new PdfTask(report, featKey, dataKey, refKey, scaleRaw, s_epsgRaw, t_epsgRaw, xRaw, yRaw);
        task.tempFile = Files.createTempFile("report_", ".pdf");
        mainTasks.put(sessionId, task);

        // Start generation
        generatePdfLogic(task,sessionId);

        if (task.isDone && Files.exists(task.tempFile)) {
            resp.setContentType("application/pdf");
            Files.copy(task.tempFile, resp.getOutputStream());
            Files.deleteIfExists(task.tempFile);
        }


        MDC.clear();
    }




    private void handleProgressStream(HttpServletRequest req, HttpServletResponse resp) throws IOException {
        String sessionId = req.getSession().getId();

        getURLParameters(req);

        if (dataKey == null){ dataKey = "";}
        if (refKey == null){ refKey = "";}
        if (scaleRaw == null){ scaleRaw = "";}
        if (s_epsgRaw == null){ s_epsgRaw = "";}
        if (t_epsgRaw == null){ t_epsgRaw = "";}
        if (xRaw == null){ xRaw = "";}
        if (yRaw == null){ yRaw = "";}



        // 1. Set the correct SSE content type
        resp.setContentType("text/event-stream");
        resp.setCharacterEncoding("UTF-8");
        resp.setHeader("Cache-Control", "no-cache");
        resp.setHeader("Connection", "keep-alive");

        logger.info("New stream request: Session={}, Report={}, FeatKey={}", sessionId, report, featKey);

        // Add SessionID to the logging context
        MDC.put("sessionId", sessionId);
        logger.info("SSE Request started for FeatKey: {} Report: {}", featKey, report);

        PdfTask existing = mainTasks.get(sessionId);
        if (existing != null && existing.future != null) existing.future.cancel(true);

        PdfTask task = new PdfTask(report, featKey, dataKey, refKey, scaleRaw, s_epsgRaw, t_epsgRaw, xRaw, yRaw);
        mainTasks.put(sessionId, task);
        task.tempFile = Files.createTempFile("report_", ".pdf");

        task.future = executor.submit(() -> {
            try {
                generatePdfLogic(task, sessionId);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        });

        // 2. Use getOutputStream instead of getWriter
        OutputStream out = resp.getOutputStream();
        int lastSentProgress = -1;
        long lastHeartbeat = System.currentTimeMillis();

        while (!task.isDone) {
            // 3. Detect client disconnect (using a zero-byte write or flush check)
            // Servlet output streams don't have a direct 'checkError',
            // but an IOException will be thrown on flush() if the client is gone.
            try {
                if (task.progress > lastSentProgress) {
                    String data = "data: " + task.progress + "\n\n";
                    out.write(data.getBytes(StandardCharsets.UTF_8));
                    out.flush();
                    lastSentProgress = task.progress;
                    lastHeartbeat = System.currentTimeMillis();
                }
                else if (System.currentTimeMillis() - lastHeartbeat > 3000) {
                    // Heartbeat comment
                    out.write(": heartbeat\n\n".getBytes(StandardCharsets.UTF_8));
                    out.flush();
                    lastHeartbeat = System.currentTimeMillis();
                }
            } catch (IOException e) {
                // This catch handles the "Client Abort" / "Broken Pipe"
                logger.error("Client disconnected detected via OutputStream.");
                task.future.cancel(true);
                mainTasks.remove(sessionId);
                return;
            }

            try { Thread.sleep(500);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            } finally {
                MDC.clear();
            }
        }

        // Final Completion Signal
        try {
            if (task.error != null) {
                String err = "event: error\ndata: " + task.error + "\n\n";
                out.write(err.getBytes(StandardCharsets.UTF_8));
                out.flush();
            } else {
                out.write("data: complete\n\n".getBytes(StandardCharsets.UTF_8));
                out.flush();
            }

        } catch (IOException ignored) {
            // Client likely closed the tab right at the end
        }
    }


    private void generatePdfLogic(PdfTask task, String sessionId) throws IOException {
        OutputStream os = Files.newOutputStream(task.tempFile);
        try {
            Document document = new Document();
            PdfWriter pdfwriter = PdfWriter.getInstance(document, os);
            document.open();

            // Start the recursive assembly
            assemblePdf(task, sessionId, document, pdfwriter, 0);

            document.close();
            os.close();
            os = null;
        } catch (Exception e) {
            logger.error("PDF Generation Failed", e);
            task.error = e.getMessage();
        } finally {
            if (os != null) try { os.close(); } catch (IOException ignored) {}
            task.isDone = true;
            logger.info("Task Done.");
        }

    }


    private void assemblePdf(PdfTask task, String sessionId, Document document, PdfWriter pdfwriter, int depth) {
        if (depth > MAX_RECURSION_DEPTH) return;
        try {
            logger.info("Temp output file created: {}", task.tempFile.toString());
            try {
                report = task.reportType;
                featKey = task.featureKey;
                dataKey = task.databaseKey;
                refKey = task.referenceKey;

                if (dataKey == null){ dataKey = "";}
                if (refKey == null){ refKey = "";}


                document.setMargins(0,0,0,0);
                pdfwriter.addViewerPreference(PdfName.FITWINDOW, PdfBoolean.PDFTRUE);
                pdfwriter.addViewerPreference(PdfName.USETHUMBS, PdfBoolean.PDFTRUE);


                p = 1;  //start adding content
                task.progress = 1;
                if (Objects.equals(report, "")) {
                    //p = 2;
                    // config bad or missing
                    logger.error("Unable to create your report.");
                    logger.error("Bad or missing report parameter.");

                } else {
                    //p = 3;
                    // config exists

                    //check for externalized config path otherwise use rootpath
                    //String configurationPath = System.getenv("CONFIGURATION_PATH");
                    String myConfigFilePath = configPath + report + ".config";
                    //logger.info("Feature Key: {}", featKey);
                    logger.info("Config file: {}", myConfigFilePath);

                    try {
                        // get the config
                        File configXMLFile = new File(myConfigFilePath);

                        DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
                        DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
                        org.w3c.dom.Document configDoc = dBuilder.parse(configXMLFile);
                        configDoc.getDocumentElement().normalize();

                        document.addTitle(getXpathString("//Settings/Output/PDF/Metadata/Title",configDoc));
                        document.addSubject(getXpathString("//Settings/Output/PDF/Metadata/Subject",configDoc));
                        String keywords = getXpathString("//Settings/Output/PDF/Metadata/Keywords",configDoc);
                        keywords = keywords.replaceAll("@featurekey", featKey);
                        keywords = keywords.replaceAll("@databasekey", dataKey);
                        keywords = keywords.replaceAll("@referencekey", refKey);
                        document.addKeywords(keywords);
                        document.addAuthor(getXpathString("//Settings/Output/PDF/Metadata/Author",configDoc));
                        document.addCreator("GeoReports");

                        PdfContentByte cb = pdfwriter.getDirectContent();

                        // Register MS Core Fonts
                        File fontDir = new File("/usr/share/fonts/truetype/msttcorefonts/");
                        if (!fontDir.exists() || fontDir.listFiles().length != 0) {
                            // Register the directory where mscorefonts are installed
                            FontFactory.registerDirectory("/usr/share/fonts/truetype/msttcorefonts/");
                        }

                        // Set defaults
                        String Value1;

                        String connectionStringSQLLabels = "Labels";
                        if (getXpathString("//Settings/QGIS/QPTLayout/SQLConnections/Labels",configDoc) != null) {
                            connectionStringSQLLabels = getXpathString("//Settings/QGIS/QPTLayout/SQLConnections/Labels",configDoc);
                        }
                        String connectionStringSQLImages = "Images";
                        if (getXpathString("//Settings/QGIS/QPTLayout/SQLConnections/Images",configDoc) != null) {
                            connectionStringSQLImages = getXpathString("//Settings/QGIS/QPTLayout/SQLConnections/Images",configDoc);
                        }

                        // check for feature keys before creating pages
                        if (!Objects.equals(featKey, ""))
                        {
                            // iterate through pages defined in the config file
                            if (getXpathNodeList("//Pages/Page",configDoc) != null) {

                                // Pages
                                NodeList xpathnodespages = getXpathNodeList("//Pages/Page",configDoc);
                                int iPageTotal = xpathnodespages.getLength();
                                for (int iPage = 0; iPage < iPageTotal; iPage++) {
                                    Node pageNode = xpathnodespages.item(iPage);
                                    int iPage1 = iPage + 1;

                                    //update task progress
                                    p = ((double) (iPage1) / iPageTotal) * 100;
                                    task.progress = (int) abs(p);

                                    boolean pageGeneration = true;
                                    String includePage = getXpathString("//Pages/Page[position()=" + iPage1 + "]/PageGeneration/@include",configDoc);
                                    switch (includePage.toLowerCase()) {
                                        case "always", "true":
                                            pageGeneration = true;
                                            break;
                                        case "sql":
                                            //producePage value determined by SQL statement returning true or false
                                            if (getXpathString("//Pages/Page[position()=" + iPage1 + "]/PageGeneration/PageGenerationSQL/SQL",configDoc) != null){
                                                Value1 = "";  //reset value string
                                                String sqlQuery = getXpathString("//Pages/Page[position()=" + iPage1 + "]/PageGeneration/PageGenerationSQL/SQL",configDoc);
                                                String connectionName = getXpathString("//Pages/Page[position()=" + iPage1 + "]/PageGeneration/PageGenerationSQL/SQL/@connection",configDoc); // Name of the database configuration to use
                                                ResultSet dsProducePage = getSQLResultSet(connectionName, sqlQuery, featKey,refKey,dataKey);
                                                if (getRowCount(dsProducePage) > 0)
                                                {
                                                    if (dsProducePage.next()) {
                                                        Value1 = dsProducePage.getString(1);
                                                    }
                                                }
                                                if (Objects.equals(Value1.toLowerCase(), "true") || Objects.equals(Value1.toLowerCase(), "false"))
                                                {
                                                    pageGeneration = Boolean.parseBoolean(Value1);
                                                }
                                            }
                                            break;
                                        default:
                                            pageGeneration = false;
                                            break;
                                    }

                                    // Start generating Pages
                                    if(pageGeneration) {
                                        // check page generation type
                                        String pageType = getXpathString("//Pages/Page[position()=" + iPage1 + "]/@type",configDoc);
                                        switch (pageType.toLowerCase()) {
                                            case "foreign":
                                                //Handle normal Foreign Page "//Pages/Page[position()=" + iPage1 + "]/ForeignPages"
                                                if(getXpathString("//Pages/Page[position()=" + iPage1 + "]/ForeignPages",configDoc) != null) {
                                                    //normal
                                                    handleForeignPage(pageNode, task, sessionId, document, pdfwriter, depth);
                                                }
                                                //Handle SQL Foreign Page "//Pages/Page[position()=" + iPage1 + "]/ForeignSQLPages"
                                                if(getXpathString("//Pages/Page[position()=" + iPage1 + "]/ForeignSQLPages",configDoc) != null) {
                                                    //via sql query
                                                    NodeList XmlNodeListForeignSQLPages = getXpathNodeList("//Pages/Page[position()=" + iPage1 + "]/ForeignSQLPages/ForeignSQLPage",configDoc);
                                                    for (int iForeignPage = 0; iForeignPage < XmlNodeListForeignSQLPages.getLength(); iForeignPage++)
                                                    {
                                                        int positionValue = iForeignPage + 1;
                                                        String connectionName = getXpathString("//Pages/Page[position()=" + iPage1 + "]/ForeignSQLPages/ForeignSQLPage[position()='" + positionValue + "']/SQL/@connection",configDoc); // Name of the database configuration to use
                                                        String sqlQuery = getXpathString("//Pages/Page[position()=" + iPage1 + "]/ForeignSQLPages/ForeignSQLPage[position()='" + positionValue + "']/SQL",configDoc);
                                                        try (ResultSet resultSet = getSQLResultSet(connectionName, sqlQuery, featKey,refKey,dataKey)) {
                                                            while (resultSet.next()) {
                                                                String foreignDoc = resultSet.getString(1);
                                                                String foreignDocImportPage = resultSet.getString(2);
                                                                String foreignDocType = resultSet.getString(3);
                                                                drawForeignPDFPages(foreignDoc, foreignDocImportPage, foreignDocType, document, pdfwriter);
                                                            }
                                                        } catch (SQLException e) {
                                                            logger.error("Database error: {}", e.getMessage());
                                                        }
                                                    }
                                                }
                                                break;
                                            case "report":
                                                String templateFile = getXpathString("//Pages/Page[position()=" + iPage1 + "]/@template",configDoc);
                                                File QGISLayoutTemplateFile = new File(configPath + templateFile);
                                                org.w3c.dom.Document layoutDoc = dBuilder.parse(QGISLayoutTemplateFile);
                                                layoutDoc.getDocumentElement().normalize();

                                                // Set page size and orientation
                                                String templatePageSize = getXpathString("//Layout/PageCollection/LayoutItem[1]/@size",layoutDoc);
                                                String[] splitResult = templatePageSize.split(",");
                                                String templatePageWidth = splitResult[0];
                                                String templatePageHeight = splitResult[1];
                                                document.setPageSize(new Rectangle(millimetersToPoints(Float.parseFloat(templatePageWidth)), millimetersToPoints(Float.parseFloat(templatePageHeight))));
                                                document.setMargins(millimetersToPoints(10),millimetersToPoints(10),millimetersToPoints(10),millimetersToPoints(10));

                                                document.newPage();

                                                //add content
                                                // Maps
                                                if (getXpathNode("//LayoutItem[@id='ppMap']", layoutDoc) != null) {

                                                    NodeList xmlNodeListTemplateMaps = getXpathNodeList("//LayoutItem[@id='ppMap']", layoutDoc);
                                                    for (int iMap = 0; iMap < xmlNodeListTemplateMaps.getLength(); iMap++) {
                                                        int iMap1 = iMap + 1;
                                                        if (getXpathNode("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]", configDoc) != null) {
                                                            String MapImageScaleFactor = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/@imageScale", configDoc);

                                                            //Map Image position


                                                            //Set Map Image position from template
                                                            String mapPosition = getXpathString("//LayoutItem[@id='ppMap'][" + iMap1 + "]/@position", layoutDoc);
                                                            splitResult = mapPosition.split(",");
                                                            MapImageX = splitResult[0];
                                                            MapImageY = splitResult[1];

                                                            //Map Image Size

                                                            //Set Map Image Size from template
                                                            String mapSize = getXpathString("//LayoutItem[@id='ppMap'][" + iMap1 + "]/@size", layoutDoc);
                                                            splitResult = mapSize.split(",");
                                                            MapImageWidth = splitResult[0];
                                                            MapImageHeight = splitResult[1];

                                                            double PageMapImageWidthMM = Double.parseDouble(MapImageWidth);

                                                            //Initiate variables for values retrieved by OGR
                                                            double OGRFeatureDiagonalLength = 0;
                                                            double OGRFeatureCentroidX = 0;
                                                            double OGRFeatureCentroidY = 0;
                                                            double FeatureScale = 0;

                                                            String FeatureURL;

                                                            boolean UseScale = true;

                                                            String MapWidth;
                                                            String MapHeight;
                                                            String MapX;
                                                            String MapY;
                                                            String MapExtentMinX = "";
                                                            String MapExtentMaxX;
                                                            String MapExtentMinY;
                                                            String MapExtentMaxY = "";


                                                            if (getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/@type", configDoc) != null) {
                                                                String MapImageType = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/@type", configDoc);

                                                                if (getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleFeature/@type", configDoc) != null) {
                                                                    //scale feature stuff here
                                                                    String ScaleFeatureMultiplier;
                                                                    String ScaleFeatureURIPath;
                                                                    String ScaleFeatureSQL;
                                                                    String ScaleFeatureSQLConnection;
                                                                    String ScaleFeatureSQLConnectionName;
                                                                    String ScaleFeatureSQLTable;
                                                                    String ScaleFeatureSQLDialect;

                                                                    String MapImageScaleFeatureType = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleFeature/@type", configDoc);

                                                                    switch (MapImageScaleFeatureType.toLowerCase()) {
                                                                        case "ogcwfs":
                                                                            ScaleFeatureMultiplier = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleFeature/@multiplier", configDoc);
                                                                            ScaleFeatureURIPath = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleFeature/URI", configDoc);
                                                                            FeatureURL = ScaleFeatureURIPath;
                                                                            FeatureURL = FeatureURL.replaceAll("@featurekey", keyEncode4URL(featKey));
                                                                            FeatureURL = FeatureURL.replaceAll("@databasekey", keyEncode4URL(dataKey));
                                                                            FeatureURL = FeatureURL.replaceAll("@referencekey", keyEncode4URL(refKey));
                                                                            if (isURLReachable(FeatureURL)) {
                                                                                ogr.RegisterAll();
                                                                                if (FeatureURL.startsWith("https")) {
                                                                                    if (Objects.equals(gdal.GetConfigOption("GDAL_HTTP_UNSAFESSL", "NO"), "NO")) {
                                                                                        gdal.SetConfigOption("GDAL_HTTP_UNSAFESSL", "YES");
                                                                                    }
                                                                                }

                                                                                DataSource dsOgr = ogr.Open(FeatureURL, 0);
                                                                                Layer layer1 = dsOgr.GetLayerByIndex(0);
                                                                                layer1.ResetReading();
                                                                                Feature feature1 = layer1.GetNextFeature();
                                                                                Geometry FeatureGeometry = feature1.GetGeometryRef();
                                                                                //look at first geometry and determine type
                                                                                if (Objects.equals(FeatureGeometry.GetGeometryRef(0).GetGeometryName(), "POINT")) {
                                                                                    //Point Feature
                                                                                    OGRFeatureDiagonalLength = Double.parseDouble(ScaleFeatureMultiplier);
                                                                                } else {
                                                                                    //Non Point Feature - use envelope of feature(s) to determine FeatureScale
                                                                                    //Envelope ext = new Envelope(); //(minX, maxX, minY, maxY)
                                                                                    double[] ext = new double[4];
                                                                                    FeatureGeometry.GetEnvelope(ext);
                                                                                    //Get centroid X and Y of envelope
                                                                                    OGRFeatureCentroidX = ext[0] + ((ext[1] - ext[0]) / 2);
                                                                                    OGRFeatureCentroidY = ext[2] + ((ext[3] - ext[2]) / 2);
                                                                                    //Check and set scale for map based on feature scale and scale values from config
                                                                                    OGRFeatureDiagonalLength = Math.sqrt(abs(Math.pow((ext[1] - ext[0]), 2) + Math.pow((ext[3] - ext[2]), 2)));
                                                                                    //Add to diagonal length so that selection shows properly
                                                                                    OGRFeatureDiagonalLength = OGRFeatureDiagonalLength * Double.parseDouble(ScaleFeatureMultiplier);
                                                                                }
                                                                                FeatureScale = (OGRFeatureDiagonalLength * 1000) / PageMapImageWidthMM;
                                                                            } else {
                                                                                logger.error("OGCWFS Feature URL unable to be retrieved: {}", FeatureURL);
                                                                            }
                                                                            break;
                                                                        case "esrirest", "ogrgeojson":
                                                                            ScaleFeatureMultiplier = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleFeature/@multiplier", configDoc);
                                                                            ScaleFeatureURIPath = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleFeature/URI", configDoc);
                                                                            FeatureURL = ScaleFeatureURIPath;
                                                                            FeatureURL = FeatureURL.replaceAll("@featurekey", keyEncode4URL(featKey));
                                                                            FeatureURL = FeatureURL.replaceAll("@databasekey", keyEncode4URL(dataKey));
                                                                            FeatureURL = FeatureURL.replaceAll("@referencekey", keyEncode4URL(refKey));
                                                                            if (isURLReachable(FeatureURL)) {
                                                                                ogr.RegisterAll();
                                                                                if (FeatureURL.startsWith("https")) {
                                                                                    if (Objects.equals(gdal.GetConfigOption("GDAL_HTTP_UNSAFESSL", "NO"), "NO")) {
                                                                                        gdal.SetConfigOption("GDAL_HTTP_UNSAFESSL", "YES");
                                                                                    }
                                                                                }

                                                                                DataSource dsOgr = ogr.Open(FeatureURL, 0);
                                                                                //Layer layer1 = dsOgr.GetLayerByIndex(0);
                                                                                Layer layer1 = dsOgr.GetLayerByName("OGRGeoJSON");


                                                                                layer1.ResetReading();
                                                                                Feature feature1 = layer1.GetNextFeature();
                                                                                Geometry FeatureGeometry = feature1.GetGeometryRef();
                                                                                //look at first geometry and determine type
                                                                                if (Objects.equals(FeatureGeometry.GetGeometryRef(0).GetGeometryName(), "POINT")) {
                                                                                    //Point Feature
                                                                                    OGRFeatureDiagonalLength = Double.parseDouble(ScaleFeatureMultiplier);
                                                                                } else {
                                                                                    //Non Point Feature - use envelope of feature(s) to determine FeatureScale
                                                                                    //Envelope ext = new Envelope(); //(minX, maxX, minY, maxY)
                                                                                    double[] ext = new double[4];
                                                                                    FeatureGeometry.GetEnvelope(ext);
                                                                                    //Get centroid X and Y of envelope
                                                                                    OGRFeatureCentroidX = ext[0] + ((ext[1] - ext[0]) / 2);
                                                                                    OGRFeatureCentroidY = ext[2] + ((ext[3] - ext[2]) / 2);
                                                                                    //Check and set scale for map based on feature scale and scale values from config
                                                                                    OGRFeatureDiagonalLength = Math.sqrt(abs(Math.pow((ext[1] - ext[0]), 2) + Math.pow((ext[3] - ext[2]), 2)));
                                                                                    //Add to diagonal length so that selection shows properly
                                                                                    OGRFeatureDiagonalLength = OGRFeatureDiagonalLength * Double.parseDouble(ScaleFeatureMultiplier);
                                                                                }
                                                                                FeatureScale = (OGRFeatureDiagonalLength * 1000) / PageMapImageWidthMM;
                                                                            } else {
                                                                                logger.error("esrirest/ogrgeojson Feature URL unable to be retrieved: {}", FeatureURL);
                                                                            }
                                                                            break;
                                                                        case "sql":
                                                                            ScaleFeatureMultiplier = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleFeature/@multiplier", configDoc);
                                                                            ScaleFeatureSQL = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleFeature/SQL", configDoc);
                                                                            ScaleFeatureSQLConnectionName = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleFeature/SQL/@connection", configDoc);
                                                                            //ScaleFeatureSQLOGRDriver = ((Node) configXpath.evaluate("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleFeature/SQL", configDoc, XPathConstants.NODE)).getAttributes().getNamedItem("ogrDriver").getTextContent();
                                                                            ScaleFeatureSQLTable = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleFeature/SQL/@table", configDoc);
                                                                            ScaleFeatureSQLDialect = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleFeature/SQL/@dialect", configDoc);

                                                                            ScaleFeatureSQLConnection = getOGRConnectionString(ScaleFeatureSQLConnectionName);


                                                                            String FeatureSQL = ScaleFeatureSQL;
                                                                            FeatureSQL = FeatureSQL.replaceAll("@featurekey", featKey);
                                                                            FeatureSQL = FeatureSQL.replaceAll("@databasekey", dataKey);
                                                                            FeatureSQL = FeatureSQL.replaceAll("@referencekey", refKey);

                                                                            if (!Objects.equals(FeatureSQL, "") && !Objects.equals(ScaleFeatureSQLConnection, "") && !Objects.equals(ScaleFeatureSQLTable, "")) {
                                                                                //Open OGR connection (Native OGR driver, NOT JDBC)
                                                                                String FeatureConnection = ScaleFeatureSQLConnection + " " + ScaleFeatureSQLTable;
                                                                                ogr.RegisterAll();

                                                                                Layer layer1;
                                                                                DataSource dsOgr = ogr.Open(FeatureConnection, 0);
                                                                                layer1 = dsOgr.ExecuteSQL(FeatureSQL, null, ScaleFeatureSQLDialect);
                                                                                layer1.ResetReading();
                                                                                Feature feature1 = layer1.GetNextFeature();

                                                                                Geometry FeatureGeometry = feature1.GetGeometryRef();

                                                                                //look at first geometry and determine type
                                                                                if (Objects.equals(FeatureGeometry.GetGeometryName(), "POINT")) {
                                                                                    //Point Feature
                                                                                    OGRFeatureDiagonalLength = Double.parseDouble(ScaleFeatureMultiplier);
                                                                                } else {
                                                                                    //Non Point Feature - use envelope of feature(s) to determine FeatureScale
                                                                                    //org.gdal.ogr.Geometry.
                                                                                    double[] ext = new double[4];
                                                                                    FeatureGeometry.GetEnvelope(ext);


                                                                                    //Get centroid X and Y of envelope
                                                                                    OGRFeatureCentroidX = ext[0] + ((ext[1] - ext[0]) / 2);
                                                                                    OGRFeatureCentroidY = ext[2] + ((ext[3] - ext[2]) / 2);

                                                                                    //Check and set scale for map based on feature scale and scale values from config
                                                                                    OGRFeatureDiagonalLength = Math.sqrt(abs(Math.pow((ext[1] - ext[0]), 2) + Math.pow((ext[3] - ext[2]), 2)));
                                                                                    //Add to diagonal length so that selection shows properly
                                                                                    OGRFeatureDiagonalLength = OGRFeatureDiagonalLength * Double.parseDouble(ScaleFeatureMultiplier);
                                                                                }
                                                                                FeatureScale = (OGRFeatureDiagonalLength * 1000) / PageMapImageWidthMM;

                                                                                dsOgr.ReleaseResultSet(layer1);
                                                                            }
                                                                            break;
                                                                        case "refkey":
                                                                            //FUTURE
                                                                            // use the url parameter refkey to supply a value for FeatureScale
                                                                            break;
                                                                        case "urlparams":
                                                                            // use url params (scale,x,y,s_epsg,t_epsg) present
                                                                            /*
                                                                            https://geospatial.whanganui.govt.nz/georeports/georeport?report=SiteMapA4PrefscaledTEST&featkey=33772&scale=auto
                                                                            https://geospatial.whanganui.govt.nz/georeports/georeport?report=SiteMapA4PrefscaledTEST&featkey=33772&scale=2000
                                                                            https://geospatial.whanganui.govt.nz/georeports/georeport?report=SiteMapA4PrefscaledTEST&featkey=33772&scale=auto&x=175.04891037940976&y=-39.933508850600234&s_epsg=4326&t_epsg=2193
                                                                            https://geospatial.whanganui.govt.nz/georeports/georeport?report=SiteMapA4PrefscaledTEST&featkey=33772&scale=2000&x=175.04891037940976&y=-39.933508850600234&s_epsg=4326&t_epsg=2193
                                                                             */
                                                                            //if (scaleRaw != null && s_epsgRaw != null && t_epsgRaw != null && xRaw != null && yRaw != null) {
                                                                            if (scaleRaw != null) {
                                                                                ScaleFeatureMultiplier = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleFeature/@multiplier", configDoc);
                                                                                ScaleFeatureURIPath = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleFeature/URI", configDoc);
                                                                                FeatureURL = ScaleFeatureURIPath;
                                                                                FeatureURL = FeatureURL.replaceAll("@featurekey", keyEncode4URL(featKey));
                                                                                FeatureURL = FeatureURL.replaceAll("@databasekey", keyEncode4URL(dataKey));
                                                                                FeatureURL = FeatureURL.replaceAll("@referencekey", keyEncode4URL(refKey));
                                                                                if (isURLReachable(FeatureURL)) {
                                                                                    ogr.RegisterAll();
                                                                                    if (FeatureURL.startsWith("https")) {
                                                                                        if (Objects.equals(gdal.GetConfigOption("GDAL_HTTP_UNSAFESSL", "NO"), "NO")) {
                                                                                            gdal.SetConfigOption("GDAL_HTTP_UNSAFESSL", "YES");
                                                                                        }
                                                                                    }

                                                                                    DataSource dsOgr = ogr.Open(FeatureURL, 0);
                                                                                    Layer layer1 = dsOgr.GetLayerByIndex(0);
                                                                                    if (layer1 != null) {
                                                                                        layer1.ResetReading();

                                                                                        if (layer1.GetFeatureCount() > 0) {
                                                                                            Feature feature1 = layer1.GetNextFeature();
                                                                                            Geometry FeatureGeometry = feature1.GetGeometryRef();
                                                                                            //look at first geometry and determine type
                                                                                            if (Objects.equals(FeatureGeometry.GetGeometryRef(0).GetGeometryName(), "POINT")) {
                                                                                                //Point Feature
                                                                                                OGRFeatureDiagonalLength = Double.parseDouble(ScaleFeatureMultiplier);
                                                                                                OGRFeatureCentroidX = FeatureGeometry.GetGeometryRef(0).GetX();
                                                                                                OGRFeatureCentroidY = FeatureGeometry.GetGeometryRef(0).GetY();
                                                                                            } else {

                                                                                                //Non Point Feature - use envelope of feature(s) to determine FeatureScale
                                                                                                double[] ext = new double[4];
                                                                                                FeatureGeometry.GetEnvelope(ext);
                                                                                                //Get centroid X and Y of envelope
                                                                                                //OGRFeatureCentroidX = ext[0] + ((ext[1] - ext[0]) / 2);
                                                                                                //OGRFeatureCentroidY = ext[2] + ((ext[3] - ext[2]) / 2);
                                                                                                OGRFeatureCentroidX = (ext[0] + ext[1]) / 2;
                                                                                                OGRFeatureCentroidY = (ext[2] + ext[3]) / 2;

                                                                                                //Check and set scale for map based on feature scale and scale values from config
                                                                                                OGRFeatureDiagonalLength = Math.sqrt(abs(Math.pow((ext[1] - ext[0]), 2) + Math.pow((ext[3] - ext[2]), 2)));
                                                                                                //Add to diagonal length so that selection shows properly
                                                                                                OGRFeatureDiagonalLength = OGRFeatureDiagonalLength * Double.parseDouble(ScaleFeatureMultiplier);
                                                                                            }
                                                                                            feature1.delete();
                                                                                        }
                                                                                    }
                                                                                    //dsOgr.ReleaseResultSet(layer1);  // Causes: A fatal error has been detected by the Java Runtime Environment

                                                                                    if (Objects.equals(scaleRaw, "auto")) {
                                                                                        // scale from url param is auto
                                                                                        // Calculate scale from the feature
                                                                                        FeatureScale = (OGRFeatureDiagonalLength * 1000) / PageMapImageWidthMM;
                                                                                    } else {
                                                                                        // scale value from url param
                                                                                        // number so convert to double
                                                                                        FeatureScale = Double.parseDouble(scaleRaw);
                                                                                    }


                                                                                } else {
                                                                                    logger.error("OGCWFS Feature URL unable to be retrieved: {}", FeatureURL);
                                                                                }
                                                                                if (s_epsgRaw != null && t_epsgRaw != null && xRaw != null && yRaw != null) {
                                                                                    CoordinateTransformation coordinateTransform = getCoordinateTransformation(s_epsgRaw, t_epsgRaw);
                                                                                    double[] t_pt = {0, 0, 0};
                                                                                    coordinateTransform.TransformPoint(t_pt, Double.parseDouble(xRaw), Double.parseDouble(yRaw), 0);
                                                                                    OGRFeatureCentroidX = t_pt[0];
                                                                                    OGRFeatureCentroidY = t_pt[1];
                                                                                    coordinateTransform.delete();
                                                                                }
                                                                            }
                                                                            break;
                                                                        default:
                                                                            break;

                                                                    }

                                                                    //scale stuff here
                                                                    //  iterate through scale values for this map from config file to find map Neat Scale
                                                                    if (getXpathNode("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleRanges", configDoc) != null) {
                                                                        //  if more than one need to iterate through each one
                                                                        NodeList XmlNodeListScales = getXpathNodeList("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleRanges/ScaleRange", configDoc);
                                                                        for (int iScale = 0; iScale < XmlNodeListScales.getLength(); iScale++) {
                                                                            Node currentScaleItem = XmlNodeListScales.item(iScale);
                                                                            String MinScale = getXpathString("@min",currentScaleItem);
                                                                            String MaxScale = getXpathString("@max",currentScaleItem);
                                                                            if ((FeatureScale > Double.parseDouble(MinScale)) && (FeatureScale <= Double.parseDouble(MaxScale))) {

                                                                                MapImageNeatScale = currentScaleItem.getTextContent();
                                                                            }
                                                                        }
                                                                    }


                                                                    //map stuff
                                                                    MapWidth = "" + round(millimetersToPoints(Float.parseFloat(MapImageWidth)) * Float.parseFloat(MapImageScaleFactor));
                                                                    MapHeight = "" + round(millimetersToPoints(Float.parseFloat(MapImageHeight)) * Float.parseFloat(MapImageScaleFactor));
                                                                    //MapZoom = "" + (PageMapImageWidthMM * Double.parseDouble(MapImageNeatScale)) / 1000;
                                                                    MapX = "" + OGRFeatureCentroidX;
                                                                    MapY = "" + OGRFeatureCentroidY;
                                                                    BigDecimal bd;
                                                                    bd = new BigDecimal(OGRFeatureCentroidX - ((Double.parseDouble(MapImageNeatScale) * (Double.parseDouble(MapImageWidth) / 1000)) / 2));
                                                                    MapExtentMinX = String.valueOf(bd.setScale(5, RoundingMode.HALF_UP).doubleValue());
                                                                    bd = new BigDecimal(OGRFeatureCentroidX + ((Double.parseDouble(MapImageNeatScale) * (Double.parseDouble(MapImageWidth) / 1000)) / 2));
                                                                    MapExtentMaxX = String.valueOf(bd.setScale(5, RoundingMode.HALF_UP).doubleValue());
                                                                    bd = new BigDecimal(OGRFeatureCentroidY - ((Double.parseDouble(MapImageNeatScale) * (Double.parseDouble(MapImageHeight) / 1000)) / 2));
                                                                    MapExtentMinY = String.valueOf(bd.setScale(5, RoundingMode.HALF_UP).doubleValue());
                                                                    bd = new BigDecimal(OGRFeatureCentroidY + ((Double.parseDouble(MapImageNeatScale) * (Double.parseDouble(MapImageHeight) / 1000)) / 2));
                                                                    MapExtentMaxY = String.valueOf(bd.setScale(5, RoundingMode.HALF_UP).doubleValue());

                                                                    String MapImageURL = "";
                                                                    //check types OGCWMS/ESRIREST/Intramaps

                                                                    switch (MapImageType.toLowerCase()) {
                                                                        case "ogcwms":
                                                                            if (UseScale) {
                                                                                // use ogc wms service for map image
                                                                                String ogcwmsURL = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/URI", configDoc);
                                                                                String ogcwmsBBOX = "&bbox=" + MapExtentMinX + "," + MapExtentMinY + "," + MapExtentMaxX + "," + MapExtentMaxY;
                                                                                String ogcwmsWidth = "&width=" + MapWidth;
                                                                                String ogcwmsHeight = "&height=" + MapHeight;
                                                                                MapImageURL = ogcwmsURL + ogcwmsWidth + ogcwmsHeight + ogcwmsBBOX;
                                                                                MapImageURL = MapImageURL.replaceAll("@featurekey", keyEncode4URL(featKey));
                                                                                MapImageURL = MapImageURL.replaceAll("@databasekey", keyEncode4URL(dataKey));
                                                                                MapImageURL = MapImageURL.replaceAll("@referencekey", keyEncode4URL(refKey));

                                                                            }
                                                                            break;
                                                                        case "esrirest":
                                                                            if (UseScale)
                                                                            {
                                                                                // use ESRI REST ImageServer service for map image (Export Image URL)
                                                                                /*
                                                                                    https://hbmaps.hbrc.govt.nz/arcgis/rest/services/Imagery/HawkesBay_Imagery_20042012/ImageServer/exportImage?
                                                                                    bbox = 1861600.0 % 2C5517600.0 % 2C2034400.0 % 2C5722800.0 &
                                                                                    bboxSR = &
                                                                                    size = &
                                                                                    imageSR = &
                                                                                    time = &
                                                                                    format = jpgpng &
                                                                                    pixelType = U8 &
                                                                                    noData = &
                                                                                    noDataInterpretation = esriNoDataMatchAny &
                                                                                    interpolation = +RSP_BilinearInterpolation &
                                                                                    compression = &
                                                                                    compressionQuality = &
                                                                                    bandIds = &
                                                                                    mosaicRule = &
                                                                                    renderingRule = &
                                                                                    f = image
                                                                                */

                                                                                String esrirestURL = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/URI", configDoc);
                                                                                // BBOX extents... BBOX=minx,miny,maxx,maxy: Bounding box corners (lower left, upper right) in SRS units.

                                                                                // Remove unecessary parameters or parameters that will be calculated
                                                                                esrirestURL = new URIBuilder(esrirestURL)
                                                                                        .removeParameter("bbox")
                                                                                        .build()
                                                                                        .toString();
                                                                                esrirestURL = new URIBuilder(esrirestURL)
                                                                                        .removeParameter("size")
                                                                                        .build()
                                                                                        .toString();
                                                                                String esrirestBBOX = "&bbox=" + MapExtentMinX + "," + MapExtentMinY + "," + MapExtentMaxX + "," + MapExtentMaxY;
                                                                                // WIDTH=output_width: Width in pixels of map picture.
                                                                                // HEIGHT=output_height: Height in pixels of map picture.
                                                                                String esrirestSize = "&size=" + MapWidth + "," + MapHeight;
                                                                                MapImageURL = esrirestURL + esrirestBBOX + esrirestSize;
                                                                                MapImageURL = MapImageURL.replace("@featurekey", featKey);
                                                                                MapImageURL = MapImageURL.replace("@datbasekey", dataKey);
                                                                                MapImageURL = MapImageURL.replace("@referencekey", refKey);
                                                                            }
                                                                            break;
                                                                        case "esrirestmapserver":
                                                                            // use ESRI REST MapServer service for map image (Export Map URL)
                                                                            /*
                                                                                https://www.topofthesouthmaps.co.nz/arcgis/rest/services/CacheAerial/MapServer/export?
                                                                                bbox=1241007.2176134433%2C5322021.548482585%2C2108073.3666623267%2C5665271.288126023&
                                                                                bboxSR=2193&
                                                                                layers=&
                                                                                layerDefs=&
                                                                                size=500%2C500&
                                                                                imageSR=&
                                                                                format=png&
                                                                                transparent=false&
                                                                                dpi=&
                                                                                time=&
                                                                                layerTimeOptions=&
                                                                                dynamicLayers=&
                                                                                gdbVersion=&
                                                                                mapScale=100000&
                                                                                rotation=&
                                                                                datumTransformations=&
                                                                                layerParameterValues=&
                                                                                mapRangeValues=&
                                                                                layerRangeValues=&
                                                                                f=image
                                                                            */
                                                                            String esrirestURL = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/URI", configDoc);
                                                                            // BBOX extents... BBOX=minx,miny,maxx,maxy: Bounding box corners (lower left, upper right) in SRS units.

                                                                            // Remove unecessary parameters or parameters that will be calculated
                                                                            esrirestURL = new URIBuilder(esrirestURL)
                                                                                    .removeParameter("bbox")
                                                                                    .build()
                                                                                    .toString();
                                                                            esrirestURL = new URIBuilder(esrirestURL)
                                                                                    .removeParameter("size")
                                                                                    .build()
                                                                                    .toString();
                                                                            esrirestURL = new URIBuilder(esrirestURL)
                                                                                    .removeParameter("mapScale")
                                                                                    .build()
                                                                                    .toString();
                                                                            esrirestURL = new URIBuilder(esrirestURL)
                                                                                    .removeParameter("dpi")
                                                                                    .build()
                                                                                    .toString();


                                                                            String newdpi = String.valueOf(Float.parseFloat(MapImageScaleFactor) * 72);
                                                                            String esrirestDPI = "&dpi=" + newdpi + "&";

                                                                            String esrirestScale = "&mapScale=" + MapImageNeatScale;

                                                                            String esrirestBBOX = "&bbox=" + MapExtentMinX + "%2C" + MapExtentMinY + "%2C" + MapExtentMaxX + "%2C" + MapExtentMaxY;
                                                                            // WIDTH=output_width: Width in pixels of map picture.
                                                                            // HEIGHT=output_height: Height in pixels of map picture.
                                                                            String esrirestSize = "&size=" + MapWidth + "%2C" + MapHeight;

                                                                            MapImageURL = esrirestURL + esrirestDPI + esrirestBBOX + esrirestSize + esrirestScale;

                                                                            MapImageURL = MapImageURL.replace("@featurekey", featKey);
                                                                            MapImageURL = MapImageURL.replace("@datbasekey", dataKey);
                                                                            MapImageURL = MapImageURL.replace("@referencekey", refKey);
                                                                            break;
                                                                        case "intramaps":
                                                                            // use INtraMaps GetMap service for map image
                                                                            //https://mapping.hdc.govt.nz/IntraMaps80/SpatialEngineWSEmbeddedMaps/getmap.ashx?Project=PropertyMaps&Module=Property&layer=Property%20Data&width=539&height=624&includeData=false&scale=1000&mapkeys=100938

                                                                            String intramapsURL = getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/URI", configDoc);
                                                                            // BBOX extents... BBOX=minx,miny,maxx,maxy: Bounding box corners (lower left, upper right) in SRS units.

                                                                            // WIDTH=output_width: Width in pixels of map picture.
                                                                            String intramapsWidth = "&width=" + MapWidth;
                                                                            // HEIGHT=output_height: Height in pixels of map picture.
                                                                            String intramapsHeight = "&height=" + MapHeight;
                                                                            // Zoom
                                                                            String intramapsZoom = "&zoom=" + (Double.parseDouble(MapImageWidth) * Double.parseDouble(MapImageNeatScale)) / 1000;
                                                                            //x
                                                                            String intramapsMapX = "&x=" + MapX;
                                                                            //y
                                                                            String intramapsMapY = "&y=" + MapY;

                                                                            MapImageURL = intramapsURL + intramapsWidth + intramapsHeight + intramapsZoom + intramapsMapX + intramapsMapY;
                                                                            MapImageURL = MapImageURL.replace("@featurekey", featKey);
                                                                            MapImageURL = MapImageURL.replace("@datbasekey", dataKey);
                                                                            MapImageURL = MapImageURL.replace("@referencekey", refKey);



                                                                            break;
                                                                        case "wmts":
                                                                            //future
                                                                            break;
                                                                        default:
                                                                            //insert unknown map type image
                                                                            break;
                                                                    }

                                                                    //get map image here
                                                                    //MapImageURL
                                                                    if (isURLReachable(MapImageURL)) {
                                                                        String scaleFactor = "" + (1 / Double.parseDouble(MapImageScaleFactor));

                                                                        drawImageFromURI(MapImageURL, MapImageX, MapImageY, scaleFactor, document);
                                                                    } else {
                                                                        logger.error("Could not get Map URL: {}", MapImageURL);
                                                                    }
                                                                }

                                                                //mapfeatures
                                                                if (getXpathString("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/MapFeatures", configDoc) != null) {
                                                                    //  iterate through each map feature
                                                                    NodeList XmlNodeListMapFeatures = getXpathNodeList("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/MapFeatures/MapFeature", configDoc);


                                                                    for (int iMapFeature = 0; iMapFeature < XmlNodeListMapFeatures.getLength(); iMapFeature++) {
                                                                        //int iMapFeature1 = iMapFeature + 1;

                                                                        Node currentMapFeature = XmlNodeListMapFeatures.item(iMapFeature);

                                                                        String MapImageMapFeatureType = getXpathString("@type",currentMapFeature);

                                                                        // Initialise ogr datasource
                                                                        DataSource dsOgr = null;
                                                                        // Initialise ogr layer
                                                                        Layer layer1 = null;
                                                                        String MapFeatureURIPath;

                                                                        switch (MapImageMapFeatureType.toLowerCase()) {
                                                                            case "ogcwfs":
                                                                                MapFeatureURIPath = getXpathString("URI", currentMapFeature);
                                                                                FeatureURL = MapFeatureURIPath;
                                                                                FeatureURL = FeatureURL.replaceAll("@featurekey", keyEncode4URL(featKey));
                                                                                FeatureURL = FeatureURL.replaceAll("@databasekey", keyEncode4URL(dataKey));
                                                                                FeatureURL = FeatureURL.replaceAll("@referencekey", keyEncode4URL(refKey));
                                                                                ogr.RegisterAll();
                                                                                //skip SSL host / certificate verification if https url
                                                                                if (FeatureURL.startsWith("https")) {
                                                                                    if (Objects.equals(gdal.GetConfigOption("GDAL_HTTP_UNSAFESSL", "NO"), "NO")) {
                                                                                        gdal.SetConfigOption("GDAL_HTTP_UNSAFESSL", "YES");
                                                                                    }
                                                                                }
                                                                                //Layer layer1;
                                                                                dsOgr = ogr.Open(FeatureURL, 0);
                                                                                layer1 = dsOgr.GetLayerByIndex(0);
                                                                                break;
                                                                            case "esrirest":
                                                                                MapFeatureURIPath = getXpathString("URI", currentMapFeature);
                                                                                FeatureURL = MapFeatureURIPath;
                                                                                FeatureURL = FeatureURL.replaceAll("@featurekey", keyEncode4URL(featKey));
                                                                                FeatureURL = FeatureURL.replaceAll("@databasekey", keyEncode4URL(dataKey));
                                                                                FeatureURL = FeatureURL.replaceAll("@referencekey", keyEncode4URL(refKey));
                                                                                ogr.RegisterAll();
                                                                                //skip SSL host / certificate verification if https url
                                                                                if (FeatureURL.startsWith("https")) {
                                                                                    if (Objects.equals(gdal.GetConfigOption("GDAL_HTTP_UNSAFESSL", "NO"), "NO")) {
                                                                                        gdal.SetConfigOption("GDAL_HTTP_UNSAFESSL", "YES");
                                                                                    }
                                                                                }
                                                                                //Layer layer1;
                                                                                dsOgr = ogr.Open(FeatureURL, 0);
                                                                                layer1 = dsOgr.GetLayerByName("OGRGeoJSON");
                                                                                break;
                                                                            case "sql":
                                                                                String MapFeatureSQL = getXpathString("SQL", currentMapFeature);
                                                                                String MapFeatureSQLConnectionName = getXpathString("SQL/@connection", currentMapFeature);
                                                                                //String MapFeatureSQLOGRDriver = getXpathString("SQL/@ogrDriver", currentMapFeature);
                                                                                String MapFeatureSQLTable = getXpathString("SQL/@table", currentMapFeature);
                                                                                String MapFeatureSQLDialect = getXpathString("SQL/@dialect", currentMapFeature);
                                                                                String MapFeatureSQLConnection = getOGRConnectionString(MapFeatureSQLConnectionName);

                                                                                String FeatureSQL = MapFeatureSQL;
                                                                                FeatureSQL = FeatureSQL.replaceAll("@featurekey", featKey);
                                                                                FeatureSQL = FeatureSQL.replaceAll("@databasekey", dataKey);
                                                                                FeatureSQL = FeatureSQL.replaceAll("@referencekey", refKey);
                                                                                if (!Objects.equals(FeatureSQL, "") && !Objects.equals(MapFeatureSQLConnection, "") && !Objects.equals(MapFeatureSQLTable, ""))
                                                                                {
                                                                                    //Open OGR connection (Native OGR driver, NOT JDBC)
                                                                                    String FeatureConnection = MapFeatureSQLConnection + " " + MapFeatureSQLTable;
                                                                                    ogr.RegisterAll();
                                                                                    //Layer layer1;
                                                                                    dsOgr = ogr.Open(FeatureConnection, 0);
                                                                                    //layer1 = dsOgr.ExecuteSQL(FeatureSQL, null, MapFeatureSQLDialect);
                                                                                    if (!Objects.equals(MapFeatureSQLDialect, "SQLITE"))
                                                                                    {
                                                                                        layer1 = dsOgr.ExecuteSQL(FeatureSQL, null, "");
                                                                                    }
                                                                                    else
                                                                                    {
                                                                                        layer1 = dsOgr.ExecuteSQL(FeatureSQL, null, MapFeatureSQLDialect);
                                                                                    }
                                                                                }
                                                                                break;
                                                                            case "intramaps":
                                                                                // cant do this as need geometry returned!!!!!!!!!
                                                                                break;
                                                                            default:
                                                                                //unknown type so error redirection here???
                                                                                break;
                                                                        }
                                                                        if (layer1 != null) {
                                                                            layer1.ResetReading();
                                                                            Feature feature1;
                                                                            Geometry FeatureGeometry;
                                                                            int featureIndex;
                                                                            for (featureIndex = 0; featureIndex < layer1.GetFeatureCount(1); featureIndex++) {

                                                                                layer1.SetNextByIndex(featureIndex);
                                                                                feature1 = layer1.GetNextFeature();
                                                                                FeatureGeometry = feature1.GetGeometryRef();

                                                                                cb = pdfwriter.getDirectContent();

                                                                                switch (FeatureGeometry.GetGeometryName()) {

                                                                                    case "POINT":

                                                                                        if (FeatureGeometry.GetPointCount() > 0) {
                                                                                            ArrayList<Point2D> featurePoints = getMapFeatureGeometryPoints(FeatureGeometry,MapImageX,MapImageY,MapExtentMinX,MapExtentMaxY,MapImageNeatScale,document);

                                                                                            if (getXpathString("Draw", currentMapFeature) != null) {

                                                                                                //  iterate through each map feature draw
                                                                                                NodeList XmlNodeListPointDraw = getXpathNodeList("Draw", currentMapFeature);



                                                                                                for (int iPointDraw = 0; iPointDraw < XmlNodeListPointDraw.getLength(); iPointDraw++) {

                                                                                                    //Node currentPointDraw = (Node) XmlNodeListMapFeatures.item(iPointDraw);
                                                                                                    Node currentPointDraw = getXpathNode(".",XmlNodeListPointDraw.item(iPointDraw));

                                                                                                    String pointDrawType = getXpathString("@type",currentPointDraw);
                                                                                                    Point2D centerPoint = featurePoints.get(0);

                                                                                                    switch (pointDrawType.toLowerCase()) {

                                                                                                        case "ellipse":
                                                                                                            if (!featurePoints.isEmpty()){
                                                                                                                //set defaults
                                                                                                                Color fillColor = new Color(255,255,255,0);
                                                                                                                Color strokeColor = new Color(0,0,0,255);
                                                                                                                float strokeWidth = 1f;
                                                                                                                Node currentBrush = getXpathNode("Brush",currentPointDraw);
                                                                                                                if (currentBrush != null) {
                                                                                                                    fillColor = getColorFromXPathNode(currentBrush);
                                                                                                                }
                                                                                                                Node currentPen = getXpathNode("Pen",currentPointDraw);
                                                                                                                if (currentPen != null) {
                                                                                                                    strokeColor = getColorFromXPathNode(currentPen);
                                                                                                                    strokeWidth = Float.parseFloat(getXpathString("@width",currentPen));
                                                                                                                }
                                                                                                                float width = Float.parseFloat(getXpathString("@width",currentPointDraw));
                                                                                                                float height = Float.parseFloat(getXpathString("@height",currentPointDraw));
                                                                                                                if (getXpathString("@offsetX",currentPointDraw) != null) {
                                                                                                                    float offsetX = Float.parseFloat(getXpathString("@offsetX",currentPointDraw));
                                                                                                                    centerPoint.setLocation(centerPoint.getX() + offsetX,centerPoint.getY());
                                                                                                                }
                                                                                                                if (getXpathString("@offsetY",currentPointDraw) != null) {
                                                                                                                    float offsetY = Float.parseFloat(getXpathString("@offsetY",currentPointDraw));
                                                                                                                    centerPoint.setLocation(centerPoint.getX(),centerPoint.getY() + offsetY);
                                                                                                                }
                                                                                                                //draw
                                                                                                                cb = pdfwriter.getDirectContent();

                                                                                                                drawMapFeatureEllipseFromCenter(document, cb,centerPoint,width,height,fillColor,strokeColor,strokeWidth);
                                                                                                            }
                                                                                                            break;
                                                                                                        case "image":
                                                                                                            String imageURL = getXpathString("@image",currentPointDraw);
                                                                                                            String imageScaleFactor = getXpathString("@scalefactor",currentPointDraw);
                                                                                                            if (getXpathString("@offsetX",currentPointDraw) != null) {
                                                                                                                float offsetX = Float.parseFloat(getXpathString("@offsetX",currentPointDraw));
                                                                                                                centerPoint.setLocation(centerPoint.getX() + offsetX,centerPoint.getY());
                                                                                                            }
                                                                                                            if (getXpathString("@offsetY",currentPointDraw) != null) {
                                                                                                                float offsetY = Float.parseFloat(getXpathString("@offsetY",currentPointDraw));
                                                                                                                centerPoint.setLocation(centerPoint.getX(),centerPoint.getY() + offsetY);
                                                                                                            }
                                                                                                            drawMapFeatureImage(imageURL, centerPoint, imageScaleFactor, document);
                                                                                                            break;
                                                                                                        case "rectangle":
                                                                                                            if (!featurePoints.isEmpty()){
                                                                                                                //set defaults
                                                                                                                Color fillColor = new Color(255,255,255,0);
                                                                                                                Color strokeColor = new Color(0,0,0,255);
                                                                                                                float strokeWidth = 1f;
                                                                                                                Node currentBrush = getXpathNode("Brush",currentPointDraw);
                                                                                                                if (currentBrush != null) {
                                                                                                                    fillColor = getColorFromXPathNode(currentBrush);
                                                                                                                }
                                                                                                                Node currentPen = getXpathNode("Pen",currentPointDraw);
                                                                                                                if (currentPen != null) {
                                                                                                                    strokeColor = getColorFromXPathNode(currentPen);
                                                                                                                    strokeWidth = Float.parseFloat(getXpathString("@width",currentPen));
                                                                                                                }
                                                                                                                float width = Float.parseFloat(getXpathString("@width",currentPointDraw));
                                                                                                                float height = Float.parseFloat(getXpathString("@height",currentPointDraw));
                                                                                                                if (getXpathString("@offsetX",currentPointDraw) != null) {
                                                                                                                    float offsetX = Float.parseFloat(getXpathString("@offsetX",currentPointDraw));
                                                                                                                    centerPoint.setLocation(centerPoint.getX() + offsetX,centerPoint.getY());
                                                                                                                }
                                                                                                                if (getXpathString("@offsetY",currentPointDraw) != null) {
                                                                                                                    float offsetY = Float.parseFloat(getXpathString("@offsetY",currentPointDraw));
                                                                                                                    centerPoint.setLocation(centerPoint.getX(),centerPoint.getY() + offsetY);
                                                                                                                }
                                                                                                                //draw
                                                                                                                cb = pdfwriter.getDirectContent();
                                                                                                                drawMapFeatureRectangleFromCenter(document, cb,centerPoint,width,height,fillColor,strokeColor,strokeWidth);
                                                                                                            }

                                                                                                            break;
                                                                                                        case "polygon":
                                                                                                            //future
                                                                                                            break;
                                                                                                        case "string":
                                                                                                            if (!featurePoints.isEmpty()){
                                                                                                                String pointDrawText = getXpathString("@text",currentPointDraw);
                                                                                                                pointDrawText = pointDrawText.replace("@featurekey", featKey);
                                                                                                                pointDrawText = pointDrawText.replace("@datbasekey", dataKey);
                                                                                                                pointDrawText =  pointDrawText.replace("@referencekey", refKey);
                                                                                                                for (int iField = 0; iField < feature1.GetFieldCount(); iField++)
                                                                                                                {
                                                                                                                    pointDrawText = pointDrawText.replace("@" + iField, feature1.GetFieldAsString(iField));
                                                                                                                }

                                                                                                                if (getXpathString("@offsetX",currentPointDraw) != null) {
                                                                                                                    float offsetX = Float.parseFloat(getXpathString("@offsetX",currentPointDraw));
                                                                                                                    centerPoint.setLocation(centerPoint.getX() + offsetX,centerPoint.getY());
                                                                                                                }
                                                                                                                if (getXpathString("@offsetY",currentPointDraw) != null) {
                                                                                                                    float offsetY = Float.parseFloat(getXpathString("@offsetY",currentPointDraw));
                                                                                                                    centerPoint.setLocation(centerPoint.getX(),centerPoint.getY() + offsetY);
                                                                                                                }

                                                                                                                //fontFamily="Arial" fontSize="8" fontStyle="Regular" red="255" green="0" blue="0" alignment="Center"
                                                                                                                String fontFamily = getXpathString("@fontFamily",currentPointDraw);
                                                                                                                int fontSize = Integer.parseInt(getXpathString("@fontSize",currentPointDraw));
                                                                                                                Color fontColor = getRGBColorFromXPathNode(currentPointDraw);
                                                                                                                String fontStyle = getXpathString("@fontStyle",currentPointDraw);


                                                                                                                String ttf = "/usr/share/fonts/truetype/msttcorefonts/" + fontFamily + ".ttf";
                                                                                                                Path linuxttfpath = Paths.get(ttf);
                                                                                                                Font font;
                                                                                                                // check if file exists in os
                                                                                                                if (Files.exists(linuxttfpath)) {
                                                                                                                    // Create the BaseFont (Identity-H handles Unicode encoding)
                                                                                                                    BaseFont bf = BaseFont.createFont(ttf, BaseFont.IDENTITY_H, BaseFont.EMBEDDED);
                                                                                                                    font = new Font(bf, fontSize);
                                                                                                                } else {
                                                                                                                    if (System.getProperty("os.name").toLowerCase().contains("linux")) {
                                                                                                                        //linux
                                                                                                                        //unknown ttf so use default
                                                                                                                        font = new Font(Font.HELVETICA, fontSize);
                                                                                                                    } else {
                                                                                                                        ttf = fontFamily.toLowerCase() + ".ttf";
                                                                                                                        BaseFont bf = BaseFont.createFont(ttf, BaseFont.IDENTITY_H, BaseFont.EMBEDDED);
                                                                                                                        font = new Font(bf, fontSize);
                                                                                                                    }
                                                                                                                }
                                                                                                                font.setColor(fontColor);
                                                                                                                int fontStyleValue = getMapFeatureTextFontStyleValue(fontStyle);
                                                                                                                font.setStyle(fontStyleValue);

                                                                                                                String alignment = getXpathString("@alignment",currentPointDraw);
                                                                                                                switch (alignment) {
                                                                                                                    case "Left":
                                                                                                                        textAlignment = ALIGN_LEFT;
                                                                                                                        break;
                                                                                                                    case "Right":
                                                                                                                        textAlignment = ALIGN_RIGHT;
                                                                                                                        break;
                                                                                                                    default:
                                                                                                                        textAlignment = ALIGN_CENTER;
                                                                                                                        break;
                                                                                                                }
                                                                                                                float rotation = 0;
                                                                                                                //draw
                                                                                                                cb = pdfwriter.getDirectContent();

                                                                                                                drawMapFeatureText(document, cb,centerPoint,pointDrawText,font,textAlignment,rotation);
                                                                                                            }

                                                                                                            break;
                                                                                                        default:
                                                                                                            //default to 2x2 ellipse

                                                                                                            break;
                                                                                                    }
                                                                                                }
                                                                                            }
                                                                                        }
                                                                                        break;
                                                                                    case "LINESTRING":
                                                                                        if (FeatureGeometry.GetPointCount() > 0) {
                                                                                            ArrayList<Point2D> featurePoints = getMapFeatureGeometryPoints(FeatureGeometry,MapImageX,MapImageY,MapExtentMinX,MapExtentMaxY,MapImageNeatScale,document);
                                                                                            if (!featurePoints.isEmpty()){
                                                                                                //set defaults
                                                                                                Color strokeColor = new Color(0,0,0,255);
                                                                                                float strokeWidth = 1f;
                                                                                                Node currentPen = getXpathNode("Pen",currentMapFeature);
                                                                                                if (currentPen != null) {
                                                                                                    strokeColor = getColorFromXPathNode(currentPen);
                                                                                                    strokeWidth = Float.parseFloat(getXpathString("@width",currentPen));
                                                                                                }
                                                                                                //draw
                                                                                                cb = pdfwriter.getDirectContent();
                                                                                                cb.rectangle(Float.parseFloat(MapImageX),Float.parseFloat(MapImageY),Float.parseFloat(MapImageWidth), Float.parseFloat(MapImageHeight));

                                                                                                drawMapFeatureLine(document, cb, featurePoints,strokeColor,strokeWidth);
                                                                                            }
                                                                                        }
                                                                                        break;
                                                                                    case "POLYGON":
                                                                                        if (FeatureGeometry.GetGeometryCount() > 0) {
                                                                                            for (var polygonIndex = 0; polygonIndex < FeatureGeometry.GetGeometryCount(); polygonIndex++) {
                                                                                                Geometry currentGeometry = FeatureGeometry.GetGeometryRef(polygonIndex);
                                                                                                ArrayList<Point2D> featurePoints = getMapFeatureGeometryPoints(currentGeometry,MapImageX,MapImageY,MapExtentMinX,MapExtentMaxY,MapImageNeatScale,document);
                                                                                                if (!featurePoints.isEmpty()){
                                                                                                    //set defaults
                                                                                                    Color fillColor = new Color(255,255,255,0);
                                                                                                    Color strokeColor = new Color(0,0,0,255);
                                                                                                    float strokeWidth = 1f;
                                                                                                    Node currentBrush = getXpathNode("Brush",currentMapFeature);
                                                                                                    if (currentBrush != null) {
                                                                                                        fillColor = getColorFromXPathNode(currentBrush);
                                                                                                    }

                                                                                                    Node currentPen = getXpathNode("Pen",currentMapFeature);
                                                                                                    if (currentPen != null) {
                                                                                                        strokeColor = getColorFromXPathNode(currentPen);
                                                                                                        strokeWidth = Float.parseFloat(getXpathString("@width",currentPen));
                                                                                                    }
                                                                                                    //draw
                                                                                                    cb = pdfwriter.getDirectContent();
                                                                                                    cb.rectangle(Float.parseFloat(MapImageX),Float.parseFloat(MapImageY),Float.parseFloat(MapImageWidth), Float.parseFloat(MapImageHeight));

                                                                                                    drawMapFeaturePolygon(document, cb, featurePoints,fillColor,strokeColor,strokeWidth);
                                                                                                }
                                                                                            }
                                                                                        }
                                                                                        break;
                                                                                    case "MULTIPOINT":
                                                                                        //FUTURE
                                                                                        break;
                                                                                    case "MULTILINESTRING":
                                                                                        if (FeatureGeometry.GetGeometryCount() > 0) {
                                                                                            for (var multiLinestringIndex = 0; multiLinestringIndex < FeatureGeometry.GetGeometryCount(); multiLinestringIndex++)
                                                                                            {
                                                                                                Geometry currentGeometry = FeatureGeometry.GetGeometryRef(multiLinestringIndex);
                                                                                                ArrayList<Point2D> featurePoints = getMapFeatureGeometryPoints(currentGeometry,MapImageX,MapImageY,MapExtentMinX,MapExtentMaxY,MapImageNeatScale,document);
                                                                                                if (!featurePoints.isEmpty()){
                                                                                                    //set defaults
                                                                                                    Color strokeColor = new Color(0,0,0,255);
                                                                                                    float strokeWidth = 1f;
                                                                                                    Node currentPen = getXpathNode("Pen",currentMapFeature);
                                                                                                    if (currentPen != null) {
                                                                                                        strokeColor = getColorFromXPathNode(currentPen);
                                                                                                        strokeWidth = Float.parseFloat(getXpathString("@width",currentPen));
                                                                                                    }
                                                                                                    //draw
                                                                                                    cb = pdfwriter.getDirectContent();
                                                                                                    cb.rectangle(Float.parseFloat(MapImageX),Float.parseFloat(MapImageY),Float.parseFloat(MapImageWidth), Float.parseFloat(MapImageHeight));

                                                                                                    drawMapFeatureLine(document, cb, featurePoints,strokeColor,strokeWidth);
                                                                                                }
                                                                                            }
                                                                                        }
                                                                                        break;
                                                                                    case "MULTIPOLYGON", "MULTISURFACE":
                                                                                        if (FeatureGeometry.GetGeometryCount() > 0) {
                                                                                            for (var multiPolygonIndex = 0; multiPolygonIndex < FeatureGeometry.GetGeometryCount(); multiPolygonIndex++)
                                                                                            {
                                                                                                var ring = FeatureGeometry.GetGeometryRef(multiPolygonIndex);
                                                                                                for (var polygonIndex = 0; polygonIndex < ring.GetGeometryCount(); polygonIndex++)
                                                                                                {
                                                                                                    var currentGeometry = ring.GetGeometryRef(polygonIndex);
                                                                                                    ArrayList<Point2D> featurePoints = getMapFeatureGeometryPoints(currentGeometry,MapImageX,MapImageY,MapExtentMinX,MapExtentMaxY,MapImageNeatScale,document);
                                                                                                    if (!featurePoints.isEmpty()){
                                                                                                        //set defaults
                                                                                                        Color fillColor = new Color(255,255,255,0);
                                                                                                        Color strokeColor = new Color(0,0,0,255);
                                                                                                        float strokeWidth = 1f;
                                                                                                        Node currentBrush = getXpathNode("Brush",currentMapFeature);
                                                                                                        if (currentBrush != null) {
                                                                                                            fillColor = getColorFromXPathNode(currentBrush);
                                                                                                        }
                                                                                                        Node currentPen = getXpathNode("Pen",currentMapFeature);
                                                                                                        if (currentPen != null) {
                                                                                                            strokeColor = getColorFromXPathNode(currentPen);
                                                                                                            strokeWidth = Float.parseFloat(getXpathString("@width",currentPen));
                                                                                                        }
                                                                                                        //draw
                                                                                                        cb = pdfwriter.getDirectContent();


                                                                                                        drawMapFeaturePolygon(document, cb, featurePoints,fillColor,strokeColor,strokeWidth);
                                                                                                    }
                                                                                                }
                                                                                            }
                                                                                        }
                                                                                        break;
                                                                                    case "MULTIGEOMETRY":
                                                                                        //future
                                                                                        break;
                                                                                    default:
                                                                                        break;
                                                                                }
                                                                            }
                                                                        }
                                                                        if (Objects.equals(MapImageMapFeatureType, "sql")) {
                                                                            dsOgr.ReleaseResultSet(layer1);
                                                                        }
                                                                    }
                                                                }
                                                            }

                                                            // if multiple maps, add scale text below each map image
                                                            if (xmlNodeListTemplateMaps.getLength() > 1)
                                                            {
                                                                String scaleText = "Scale 1:" + MapImageNeatScale;
                                                                Font scaleTextFont = FontFactory.getFont(FontFactory.HELVETICA, 10, Color.BLACK);
                                                                float scaleTextLength = scaleText.length();
                                                                float x = Float.parseFloat(MapImageX);
                                                                float y = Float.parseFloat(MapImageY) + Float.parseFloat(MapImageHeight)-5;
                                                                float scaleTextBorderWidth = 0.1f;
                                                                drawRectangle(cb, x, y, scaleTextLength * 2 + 2.5f, 5, Color.WHITE, Color.BLACK,scaleTextBorderWidth, document);
                                                                drawText(cb, x, y+1, scaleTextLength * 2 + 2.5f, 4, scaleText, scaleTextFont,1,false,document);
                                                            }
                                                        }
                                                    }
                                                }

                                                // Floating Images
                                                //(String) configXpath.evaluate("//Pages/Page[position()=" + iPage1 + "]",configDoc,XPathConstants.STRING)
                                                if (getXpathNode("//Pages/Page[position()=" + iPage1 + "]/FloatingImages",configDoc) != null) {
                                                     if (getXpathNodeList("//Pages/Page[position()=" + iPage1 + "]/FloatingImages/FloatingImage",configDoc) != null) {
                                                        NodeList XmlNodeListFloatingImages = getXpathNodeList("//Pages/Page[position()=" + iPage1 + "]/FloatingImages/FloatingImage",configDoc);
                                                        for (int iFloatingImage = 0; iFloatingImage < XmlNodeListFloatingImages.getLength(); iFloatingImage++) {



                                                            //Node XmlCurrentFloatingImage = (Node) configXpath.evaluate("//Pages/Page[position()=" + iPage1 + "]/FloatingImages/FloatingImage[position()=" + iFloatingImage + "]", configDoc, XPathConstants.NODE);
                                                            Node XmlCurrentFloatingImage = getXpathNode(".",XmlNodeListFloatingImages.item(iFloatingImage));

                                                            String FloatingImageType = getXpathString("@type",XmlCurrentFloatingImage);
                                                            switch (FloatingImageType.toLowerCase()) {
                                                                case "file":
                                                                    String ImageFile = getXpathString("@file",XmlCurrentFloatingImage);
                                                                    String ImageFileX = getXpathString("@x",XmlCurrentFloatingImage);
                                                                    String ImageFileY = getXpathString("@y",XmlCurrentFloatingImage);
                                                                    String ImageFileMultiplier = getXpathString("@multiplier",XmlCurrentFloatingImage);
                                                                    drawImageFromURI(ImageFile,ImageFileX,ImageFileY,ImageFileMultiplier,document);
                                                                    break;
                                                                case "uri":
                                                                    //String ImageURI = ((String) configXpath.evaluate("//Pages/Page[position()=" + iPage1 + "]/FloatingImages/FloatingImage[position()=" + iFloatingImage + "]/URI", configDoc, XPathConstants.STRING));
                                                                    String ImageURI = getXpathString(".",XmlCurrentFloatingImage);
                                                                    String ImageURIX = getXpathString("@x",XmlCurrentFloatingImage);
                                                                    String ImageURIY = getXpathString("@y",XmlCurrentFloatingImage);
                                                                    String ImageURIMultiplier = getXpathString("@multiplier",XmlCurrentFloatingImage);
                                                                    drawImageFromURI(ImageURI,ImageURIX,ImageURIY,ImageURIMultiplier,document);
                                                                    break;
                                                                case "sql":
                                                                    // EXPERIMENTAL!
                                                                    /*
                                                                    String ImageSQL = getXpathString("SQL",XmlCurrentFloatingImage);;
                                                                    String ImageSQLX = getXpathString("@x",XmlCurrentFloatingImage);
                                                                    String ImageSQLY = getXpathString("@y",XmlCurrentFloatingImage);
                                                                    String ImageSQLMultiplier = getXpathString("@multiplier",XmlCurrentFloatingImage);

                                                                    String ImageSQLConnectionName = getXpathString("SQL/@connection", XmlCurrentFloatingImage);
                                                                    //String ImageSQLOGRDriver = ((Node) configXpath.evaluate("//Pages/Page[position()=" + iPage1 + "]/MapImage[position()=" + iMap1 + "]/ScaleFeature/SQL", configDoc, XPathConstants.NODE)).getAttributes().getNamedItem("ogrDriver").getTextContent();
                                                                    String ImageSQLTable = getXpathString("SQL/@table", XmlCurrentFloatingImage);
                                                                    String ImageSQLDialect = getXpathString("SQL/@dialect", XmlCurrentFloatingImage);
                                                                    String ImageSQLConnection = getOGRConnectionString(dbConfigFilePath, ImageSQLConnectionName);

                                                                    ImageSQL = ImageSQL.replaceAll("@featurekey", featKey);
                                                                    ImageSQL = ImageSQL.replaceAll("@databasekey", dataKey);
                                                                    ImageSQL = ImageSQL.replaceAll("@referencekey", refKey);

                                                                    ResultSet ImageSQLRS = getSQLResultSet(ImageSQLConnectionName, ImageSQL, FeatureKeys, ReferenceKey, DatabaseKey);

                                                                    //to do
                                                                    //



                                                                    //drawImage(ImageURI,ImageSQLX,ImageSQLY,ImageSQLMultiplier,document);

                                                                     */


                                                                    break;
                                                                default:
                                                                    //insert unknown type image
                                                                    break;

                                                            }
                                                       }
                                                    }
                                                }




                                                // Borders
                                                if (getXpathNodeList("//LayoutItem[@shapeType='1']", layoutDoc) != null) {
                                                    NodeList XmlNodeListTemplateBorders = getXpathNodeList("//LayoutItem[@shapeType='1']", layoutDoc);
                                                    for (int iBorder = 0; iBorder < XmlNodeListTemplateBorders.getLength(); iBorder++)
                                                    {
                                                        Node currentBorder = XmlNodeListTemplateBorders.item(iBorder);

                                                        //set defaults
                                                        Color fillColor = new Color(255,255,255,0);
                                                        Color strokeColor = new Color(0,0,0,255);
                                                        float strokeWidth = 1f;

                                                        Node backgroundColor = getXpathNode("BackgroundColor", currentBorder);
                                                        if (backgroundColor != null) {
                                                            fillColor = getColorFromXPathNode(backgroundColor);
                                                        }
                                                        Node frameColor = getXpathNode("FrameColor", currentBorder);
                                                        if (frameColor != null) {
                                                            strokeColor = getColorFromXPathNode(frameColor);
                                                        }
                                                        if (getXpathString("@outlineWidthM",currentBorder) != null) {
                                                            String outlineWidthM = getXpathString("@outlineWidthM",currentBorder);
                                                            splitResult = outlineWidthM.split(",");
                                                            strokeWidth = Float.parseFloat(splitResult[0]);
                                                        }

                                                        //position
                                                        //Set defaults
                                                        String positionX;
                                                        String positionY;
                                                        //Set position from template
                                                        String positionText = getXpathString("@position",currentBorder);
                                                        splitResult = positionText.split(",");
                                                        positionX = splitResult[0];
                                                        positionY = splitResult[1];

                                                        //Size
                                                        //Set defaults
                                                        String sizeWidth;
                                                        String sizeHeight;
                                                        //Set Size from template
                                                        String sizeText = getXpathString("@size",currentBorder);
                                                        splitResult = sizeText.split(",");
                                                        sizeWidth = splitResult[0];
                                                        sizeHeight = splitResult[1];

                                                        //Draw the border

                                                        cb = pdfwriter.getDirectContent();
                                                        cb.saveState();
                                                        cb.setLineWidth(strokeWidth);
                                                        cb.setRGBColorStroke(strokeColor.getRed(),strokeColor.getGreen(),strokeColor.getBlue(),strokeColor.getAlpha());
                                                        if (Objects.equals(getXpathString("symbol/layer[last()]/prop[@k='style']/@v", currentBorder), "no")) {
                                                            //Border with no brush
                                                            cb.setRGBColorFill(fillColor.getRed(),fillColor.getGreen(),fillColor.getBlue(),0);
                                                        } else {
                                                            //Border with solid brush
                                                            cb.setRGBColorFill(fillColor.getRed(),fillColor.getGreen(),fillColor.getBlue(),fillColor.getAlpha());
                                                        }

                                                        // draw a rectangle
                                                        cb.rectangle(millimetersToPoints(Float.parseFloat(positionX)), getTopY(document,millimetersToPoints(Float.parseFloat(positionY))) - millimetersToPoints(Float.parseFloat(sizeHeight)), millimetersToPoints(Float.parseFloat(sizeWidth)), millimetersToPoints(Float.parseFloat(sizeHeight)));
                                                        cb.stroke();
                                                        cb.restoreState();
                                                        cb.sanityCheck();
                                                    }
                                                }

                                                // Images
                                                if (getXpathNodeList("//LayoutItem[@id='ppImage']", layoutDoc) != null) {
                                                    NodeList XmlNodeListImages = getXpathNodeList("//LayoutItem[@id='ppImage']", layoutDoc);
                                                    for (int iImage = 0; iImage < XmlNodeListImages.getLength(); iImage++)
                                                    {
                                                        Node currentImage = XmlNodeListImages.item(iImage);
                                                        //int iImage1 = iImage + 1;
                                                        String ImageFile = getXpathString("@file",currentImage);
                                                        if (!Objects.equals(ImageFile, ""))
                                                        {
                                                            //Image scaling
                                                            //Set defaults
                                                            String ScaleImageByValue = "1";
                                                            //outlineWidthM
                                                            if (getXpathString("@outlineWidthM",currentImage) != null) {
                                                                String RawScaleImageBy = getXpathString("@outlineWidthM",currentImage);
                                                                splitResult = RawScaleImageBy.split(",");
                                                                ScaleImageByValue = splitResult[0];
                                                            }
                                                            //Image position
                                                            //Set defaults
                                                            String ImagePositionX = "0";
                                                            String ImagePositionY = "0";
                                                            if (getXpathString("@position",currentImage) != null) {
                                                                String imagePosition = getXpathString("@position",currentImage);
                                                                splitResult = imagePosition.split(",");
                                                                ImagePositionX = splitResult[0];
                                                                ImagePositionY = splitResult[1];
                                                            }
                                                            drawImageFromFilePath(ImageFile, ImagePositionX, ImagePositionY, ScaleImageByValue, document);
                                                        }
                                                    }
                                                }

                                                // Images via SQL
                                                if (getXpathNode("//LayoutItem[@id='ppImageSQL']", layoutDoc) != null) {
                                                    NodeList XmlNodeListImages = getXpathNodeList("//LayoutItem[@id='ppImageSQL']", layoutDoc);
                                                    for (int iImage = 0; iImage < XmlNodeListImages.getLength(); iImage++)
                                                    {
                                                        Node currentImage = XmlNodeListImages.item(iImage);
                                                        String ImageSQLURI = "";
                                                        String ScaleImageByValue = "1";
                                                        String ImagePositionX = "0";
                                                        String ImagePositionY = "0";

                                                        String ImageSQL = getXpathString("@labelText",currentImage);
                                                        ResultSet ImageSQLDS = getSQLResultSet(connectionStringSQLImages,ImageSQL,featKey,refKey,dataKey);
                                                        if (getRowCount(ImageSQLDS) > 0)
                                                        {
                                                            if (ImageSQLDS.next()) {
                                                                ImageSQLURI = ImageSQLDS.getString(1);
                                                            }
                                                        }

                                                        //outlineWidthM
                                                        if (getXpathString("@outlineWidthM",currentImage) != null) {
                                                            String RawScaleImageBy = getXpathString("@outlineWidthM",currentImage);
                                                            splitResult = RawScaleImageBy.split(",");
                                                            ScaleImageByValue = splitResult[0];
                                                        }
                                                        //Image position
                                                        if (getXpathString("@position",currentImage) != null) {
                                                            String imagePosition = getXpathString("@position",currentImage);
                                                            splitResult = imagePosition.split(",");
                                                            ImagePositionX = splitResult[0];
                                                            ImagePositionY = splitResult[1];
                                                        }

                                                        //check for http
                                                        if (!Objects.equals(ImageSQLURI, "") && ImageSQLURI.toLowerCase().startsWith("http")){
                                                            drawImageFromURI(ImageSQLURI, ImagePositionX, ImagePositionY, ScaleImageByValue, document);
                                                        } else {
                                                            drawImageFromFilePath(ImageSQLURI, ImagePositionX, ImagePositionY, ScaleImageByValue, document);
                                                        }
                                                    }
                                                }

                                                // Labels
                                                if (getXpathNode("//LayoutItem[@id='ppLabel']", layoutDoc) != null) {
                                                    NodeList XmlNodeListLabels = getXpathNodeList("//LayoutItem[@id='ppLabel']", layoutDoc);
                                                    for (int iLabel = 0; iLabel < XmlNodeListLabels.getLength(); iLabel++)
                                                    {
                                                        Node currentLabel = XmlNodeListLabels.item(iLabel);
                                                        String LabelText = getXpathString("@labelText",currentLabel);
                                                        LabelText = LabelText.replaceAll("@featurekey", featKey);
                                                        LabelText = LabelText.replaceAll("@databasekey", dataKey);
                                                        LabelText = LabelText.replaceAll("@referencekey", refKey);
                                                        if (!Objects.equals(LabelText, ""))
                                                        {
                                                            setLabelVariables(currentLabel);
                                                            Font font = setFontStylesFromQPT(currentLabel);
                                                            drawText(cb,LabelPositionX,LabelPositionY,LabelWidth,LabelHeight,LabelText,font,textAlignment, false, document);
                                                        }
                                                    }
                                                }

                                                // Labels via SQL
                                                if (getXpathNode("//LayoutItem[@id='ppLabelSQL']", layoutDoc) != null) {
                                                    NodeList XmlNodeListLabels = getXpathNodeList("//LayoutItem[@id='ppLabelSQL']", layoutDoc);
                                                    for (int iLabel = 0; iLabel < XmlNodeListLabels.getLength(); iLabel++)
                                                    {
                                                        Node currentLabel = XmlNodeListLabels.item(iLabel);
                                                        String LabelText = "";
                                                        String LabelSQL = getXpathString("@labelText",currentLabel);
                                                        ResultSet LabelSQLDS = getSQLResultSet(connectionStringSQLLabels,LabelSQL,featKey,refKey,dataKey);
                                                        if (getRowCount(LabelSQLDS) > 0)
                                                        {
                                                            if (LabelSQLDS.next()) {
                                                                LabelText = LabelSQLDS.getString(1);
                                                            }
                                                        }
                                                        LabelText = LabelText.replaceAll("@featurekey", featKey);
                                                        LabelText = LabelText.replaceAll("@databasekey", dataKey);
                                                        LabelText = LabelText.replaceAll("@referencekey", refKey);

                                                        if (!Objects.equals(LabelText, ""))
                                                        {
                                                            setLabelVariables(currentLabel);
                                                            Font font = setFontStylesFromQPT(currentLabel);
                                                            drawText(cb,LabelPositionX,LabelPositionY,LabelWidth,LabelHeight,LabelText,font,textAlignment, false, document);
                                                        }
                                                    }
                                                }

                                                // Labels via WFS
                                                if (getXpathNode("//LayoutItem[@id='ppLabelWFS']", layoutDoc) != null) {
                                                    NodeList XmlNodeListLabels = getXpathNodeList("//LayoutItem[@id='ppLabelWFS']", layoutDoc);
                                                    for (int iLabel = 0; iLabel < XmlNodeListLabels.getLength(); iLabel++)
                                                    {
                                                        Node currentLabel = XmlNodeListLabels.item(iLabel);
                                                        String LabelText = "";

                                                        // Initialise ogr datasource
                                                        DataSource dsOgr;
                                                        // Initialise ogr layer
                                                        Layer layer1;

                                                        String dataURL = getXpathString("@labelText",currentLabel);
                                                        dataURL = dataURL.replaceAll("@featurekey", keyEncode4URL(featKey));
                                                        dataURL = dataURL.replaceAll("@databasekey", keyEncode4URL(dataKey));
                                                        dataURL = dataURL.replaceAll("@referencekey", keyEncode4URL(refKey));

                                                        String propertyName = getQueryStringPropertyName(dataURL);

                                                        ogr.RegisterAll();
                                                        //skip SSL host / certificate verification if https url
                                                        if (dataURL.startsWith("https")) {
                                                            if (Objects.equals(gdal.GetConfigOption("GDAL_HTTP_UNSAFESSL", "NO"), "NO")) {
                                                                gdal.SetConfigOption("GDAL_HTTP_UNSAFESSL", "YES");
                                                            }
                                                        }
                                                        //Layer layer1;
                                                        dsOgr = ogr.Open(dataURL, 0);
                                                        layer1 = dsOgr.GetLayerByIndex(0);

                                                        if (!Objects.equals(propertyName, ""))
                                                        {
                                                            String FeatureSQL = "SELECT \"" + propertyName.replace(",", "\", \"") + "\" FROM \"" + layer1.GetName() + "\"";
                                                            layer1 = dsOgr.ExecuteSQL(FeatureSQL, null, "SQLITE");
                                                        }


                                                        if (layer1 != null)
                                                        {
                                                            layer1.ResetReading();
                                                            Feature feature1;
                                                            int featureIndex;
                                                            for (featureIndex = 0; featureIndex < layer1.GetFeatureCount(1); featureIndex++) {
                                                                layer1.SetNextByIndex(featureIndex);
                                                                feature1 = layer1.GetNextFeature();
                                                                //column values for each feature
                                                                for (int iField = 0; iField < feature1.GetFieldCount(); iField++)
                                                                {
                                                                    LabelText = feature1.GetFieldAsString(iField);
                                                                }
                                                                feature1.delete(); // Important: Manually free native memory
                                                            }

                                                        }
                                                        dsOgr.ReleaseResultSet(layer1);
                                                        LabelText = LabelText.replaceAll("@featurekey", featKey);
                                                        LabelText = LabelText.replaceAll("@databasekey", dataKey);
                                                        LabelText = LabelText.replaceAll("@referencekey", refKey);
                                                        if (!Objects.equals(LabelText, ""))
                                                        {
                                                            setLabelVariables(currentLabel);
                                                            Font font = setFontStylesFromQPT(currentLabel);
                                                            drawText(cb,LabelPositionX,LabelPositionY,LabelWidth,LabelHeight,LabelText,font,textAlignment, false, document);
                                                        }
                                                    }
                                                }

                                                // Label - Scale Text
                                                if (getXpathNode("//LayoutItem[@id='ppMap']", layoutDoc) != null) {
                                                    if (getXpathNode("//LayoutItem[@id='ppScaleText']", layoutDoc) != null) {
                                                        Node currentLabel = getXpathNode("//LayoutItem[@id='ppScaleText']", layoutDoc);
                                                        // Set default Neat Scale variable for scale calcs
                                                        String textScale = MapImageNeatScale;

                                                        if (!Objects.equals(textScale, "")) {
                                                            setLabelVariables(currentLabel);
                                                            Font font = setFontStylesFromQPT(currentLabel);
                                                            drawText(cb, LabelPositionX, LabelPositionY, LabelWidth, LabelHeight, textScale, font, textAlignment, false, document);
                                                        }
                                                    }
                                                }

                                                // Label - Page Size
                                                if (getXpathNode("//LayoutItem[@id='ppPageSize']", layoutDoc) != null) {
                                                    Node currentLabel = getXpathNode("//LayoutItem[@id='ppPageSize']", layoutDoc);
                                                    Rectangle pageSize = document.getPageSize();
                                                    float width = pageSize.getWidth();
                                                    float height = pageSize.getHeight();
                                                    String textPageSize = "Original Size: " + width + " x " + height + " mm";

                                                    if (!Objects.equals(textPageSize, ""))
                                                    {
                                                        setLabelVariables(currentLabel);
                                                        Font font = setFontStylesFromQPT(currentLabel);
                                                        drawText(cb,LabelPositionX,LabelPositionY,LabelWidth,LabelHeight,textPageSize,font,textAlignment,false, document);
                                                    }
                                                }

                                                // Label - Current Date
                                                if (getXpathNode("//LayoutItem[@id='ppCurrentDate']", layoutDoc) != null) {
                                                    Node currentLabel = getXpathNode("//LayoutItem[@id='ppCurrentDate']", layoutDoc);
                                                    ZonedDateTime explicitNow = ZonedDateTime.now(ZoneId.systemDefault());

                                                    DateTimeFormatter formatter = DateTimeFormatter.ofPattern("EEEE, MMMM dd, yyyy"); //e.g. "dd/MM/yyyy HH:mm"
                                                    String textDateTime = explicitNow.format(formatter);

                                                    if (!Objects.equals(textDateTime, ""))
                                                    {
                                                        setLabelVariables(currentLabel);
                                                        Font font = setFontStylesFromQPT(currentLabel);
                                                        drawText(cb,LabelPositionX,LabelPositionY,LabelWidth,LabelHeight,textDateTime,font,textAlignment,false, document);
                                                    }
                                                }

                                                // Label - Title
                                                if (getXpathNode("//LayoutItem[@id='ppTitle']", layoutDoc) != null) {
                                                    NodeList XmlNodeListLabels = getXpathNodeList("//LayoutItem[@id='ppTitle']", layoutDoc);
                                                    for (int iLabel = 0; iLabel < XmlNodeListLabels.getLength(); iLabel++)
                                                    {
                                                        Node currentLabel = XmlNodeListLabels.item(iLabel);
                                                        String TitleText = getXpathString("@labelText",currentLabel);
                                                        if (getXpathString("//Pages/Page[position()=" + iPage1 + "]/@title",configDoc ) != null)
                                                        {
                                                            TitleText = getXpathString("//Pages/Page[position()=" + iPage1 + "]/@title",configDoc );
                                                            TitleText = TitleText.replaceAll("@featurekey", featKey);
                                                            TitleText = TitleText.replaceAll("@databasekey", dataKey);
                                                            TitleText = TitleText.replaceAll("@referencekey", refKey);
                                                        }
                                                        if (!Objects.equals(TitleText, ""))
                                                        {
                                                            setLabelVariables(currentLabel);
                                                            Font font = setFontStylesFromQPT(currentLabel);
                                                            drawRectangle(cb,LabelPositionX-1,LabelPositionY-1,LabelWidth+2,LabelHeight+2,getColorFromXPathNode(getXpathNode("BackgroundColor",currentLabel)),getColorFromXPathNode(getXpathNode("FrameColor",currentLabel)), 0.1f,document);
                                                            drawText(cb,LabelPositionX,LabelPositionY,LabelWidth,LabelHeight,TitleText,font,textAlignment,true, document);
                                                        }
                                                    }
                                                }

                                                // Data Tables
                                                if (getXpathNode("//LayoutItem[@id='ppData']", layoutDoc) != null) {
                                                    Node dataLayout = getXpathNode("//LayoutItem[@id='ppData']", layoutDoc);
                                                    //Set defaults

                                                    //Data Table position
                                                    //Set defaults
                                                    String DataTableX;
                                                    String DataTableY;
                                                    //Set Data Table position from template
                                                    String mapPosition = getXpathString("@position", dataLayout);
                                                    splitResult = mapPosition.split(",");
                                                    DataTableX = splitResult[0];
                                                    DataTableY = splitResult[1];

                                                    //Data Table Size
                                                    //Set defaults
                                                    String DataTableWidth;
                                                    //String DataTableHeight = "0";
                                                    //Set Map Image Size from template
                                                    String mapSize = getXpathString("@size", dataLayout);
                                                    splitResult = mapSize.split(",");
                                                    DataTableWidth = splitResult[0];
                                                    //DataTableHeight = splitResult[1];




                                                    // reset default fonts
                                                    titleFont = FontFactory.getFont(FontFactory.HELVETICA_BOLD, 12, Color.BLACK);
                                                    descriptionFont = FontFactory.getFont(FontFactory.HELVETICA, 10, Color.BLACK);
                                                    headerFont = FontFactory.getFont(FontFactory.HELVETICA_BOLD, 10, Color.BLACK);
                                                    cellFont = FontFactory.getFont(FontFactory.HELVETICA, 10, Color.BLACK);

                                                    // reset default background colors
                                                    titleColor = new Color(255, 255, 255,0);
                                                    descriptionColor = new Color(255, 255, 255,0);
                                                    //Color headerColor = new Color(255, 255, 255,255);
                                                    headerColor = Color.LIGHT_GRAY;
                                                    cellColor = new Color(255, 255, 255,255);
                                                    alternateCellColor = new Color(245, 245, 245,255);

                                                    // reset default border colors
                                                    titleBorderColor = new Color(0, 0, 0,0);
                                                    descriptionBorderColor = new Color(0, 0, 0,0);
                                                    headerBorderColor = new Color(0, 0, 0,255);
                                                    cellBorderColor = new Color(0, 0, 0,255);
                                                    alternateCellBorderColor = new Color(0, 0, 0,255);

                                                    // reset default border width
                                                    titleBorderWidth = 0.1f;
                                                    descriptionBorderWidth = 0.1f;
                                                    headerBorderWidth = 0.1f;
                                                    cellBorderWidth = 0.1f;
                                                    alternateCellBorderWidth = 0.1f;

                                                    // Override Default Styles with QGIS Template defined styles if defined
                                                    if (getXpathNode("//LayoutItem[@id='ppDataTableTitleStyle']",layoutDoc) != null) {
                                                        setDataStylesFromQPT("Title",getXpathNode("//LayoutItem[@id='ppDataTableTitleStyle']",layoutDoc));
                                                    }
                                                    if (getXpathNode("//LayoutItem[@id='ppDataTableDescriptionStyle']",layoutDoc) != null) {
                                                        setDataStylesFromQPT("Description",getXpathNode("//LayoutItem[@id='ppDataTableDescriptionStyle']",layoutDoc));
                                                    }
                                                    if (getXpathNode("//LayoutItem[@id='ppDataTableHeadingStyle']",layoutDoc) != null) {
                                                        setDataStylesFromQPT("Header",getXpathNode("//LayoutItem[@id='ppDataTableHeadingStyle']",layoutDoc));
                                                    }
                                                    if (getXpathNode("//LayoutItem[@id='ppDataTableRowDefaultStyle']",layoutDoc) != null) {
                                                        setDataStylesFromQPT("Cell",getXpathNode("//LayoutItem[@id='ppDataTableRowDefaultStyle']",layoutDoc));
                                                    }
                                                    if (getXpathNode("//LayoutItem[@id='ppDataTableRowAlternateStyle']",layoutDoc) != null) {
                                                        setDataStylesFromQPT("CellAlternate",getXpathNode("//LayoutItem[@id='ppDataTableRowAlternateStyle']",layoutDoc));
                                                    }


                                                    // get data
                                                    if (getXpathString("//Pages/Page[position()=" + iPage1 + "]/DataTables",configDoc) != null) {

                                                        //SQL Data Table
                                                        if (getXpathNodeList("//Pages/Page[position()=" + iPage1 + "]/DataTables/SQLDataTable",configDoc) != null) {
                                                            NodeList XmlNodeListSQLData = getXpathNodeList("//Pages/Page[position()=" + iPage1 + "]/DataTables/SQLDataTable",configDoc);
                                                            ArrayList<ArrayList<PdfPTable>> SQLDataTables = new ArrayList<>();

                                                            for (int iSQLData = 0; iSQLData < XmlNodeListSQLData.getLength(); iSQLData++)
                                                            {

                                                                Node XmlCurrentSQLDataNode = getXpathNode(".",XmlNodeListSQLData.item(iSQLData));


                                                                SQLDataTables.add(new ArrayList<>());
                                                                //int iSQLData1 = iSQLData + 1;
                                                                if (getXpathString("SQL",XmlCurrentSQLDataNode) != null)
                                                                {


                                                                    String dataCaption = getXpathString("@caption", XmlCurrentSQLDataNode);
                                                                    String dataDescription = "";
                                                                    if (getXpathString("@description", XmlCurrentSQLDataNode) != null) {
                                                                        dataDescription = getXpathString("@description", XmlCurrentSQLDataNode);
                                                                    }
                                                                    String dataMessage = getXpathString("@nodata",XmlCurrentSQLDataNode);
                                                                    String dataConnection = getXpathString("SQL/@connection",XmlCurrentSQLDataNode);
                                                                    String dataSQL = getXpathString("SQL",XmlCurrentSQLDataNode);
                                                                    String dataColWidths = getXpathString("SQL/@colwidths",XmlCurrentSQLDataNode);

                                                                    // Data resultset
                                                                    ResultSet rs = getSQLResultSet(dataConnection, dataSQL, featKey, refKey, dataKey);
                                                                    ResultSetMetaData resultSetMetaData = rs.getMetaData();


                                                                    // Data Title Table
                                                                    //setDataTableSingleCell(dataCaption, titleFont, titleColor, titleBorderColor, titleBorderWidth, document);
                                                                    SQLDataTables.get(iSQLData).add(getDataTableSingleCell(dataCaption, titleFont, titleColor, titleBorderColor, titleBorderWidth));

                                                                    if (!rs.isBeforeFirst()) {
                                                                        // No Data Message Table
                                                                        //setDataTableSingleCell(dataMessage, descriptionFont, descriptionColor, descriptionBorderColor, descriptionBorderWidth, document);
                                                                        SQLDataTables.get(iSQLData).add(getDataTableSingleCell(dataMessage, descriptionFont, descriptionColor, descriptionBorderColor, descriptionBorderWidth));
                                                                    } else {
                                                                        // Data Description Table
                                                                        PdfPTable descriptionTable = getDataTableSingleCell(dataDescription, descriptionFont, descriptionColor, descriptionBorderColor, descriptionBorderWidth);
                                                                        if (descriptionTable.size() > 0) {
                                                                            SQLDataTables.get(iSQLData).add(descriptionTable);
                                                                        }
                                                                        // Data Table
                                                                        //setDataTableFromResultSet(resultSetMetaData, dataColWidths, headerFont, headerColor, headerBorderColor, headerBorderWidth, rs, cellFont, cellColor, cellBorderColor, cellBorderWidth, alternateCellColor, alternateCellBorderColor, alternateCellBorderWidth, document);
                                                                        SQLDataTables.get(iSQLData).add(getDataTableFromResultSet(resultSetMetaData, dataColWidths, headerFont, headerColor, headerBorderColor, headerBorderWidth, rs, cellFont, cellColor, cellBorderColor, cellBorderWidth, alternateCellColor, alternateCellBorderColor, alternateCellBorderWidth));
                                                                    }
                                                                }
                                                            }
                                                            drawNestedTables(pdfwriter, document,SQLDataTables,Float.parseFloat(DataTableX),Float.parseFloat(DataTableY),Float.parseFloat(DataTableWidth));
                                                        }

                                                        //OGC WFS Data (Many)
                                                        if (getXpathNodeList("//Pages/Page[position()=" + iPage1 + "]/DataTables/OGCWFSDataTable",configDoc) != null) {
                                                            NodeList XmlNodeListOGCWFS = getXpathNodeList("//Pages/Page[position()=" + iPage1 + "]/DataTables/OGCWFSDataTable",configDoc);
                                                            ArrayList<ArrayList<PdfPTable>> OGCWFSDataTables = new ArrayList<>();

                                                            for (int iOGCWFS = 0; iOGCWFS < XmlNodeListOGCWFS.getLength(); iOGCWFS++)
                                                            {
                                                                Node XmlCurrentOGCWFSTable = getXpathNode(".",XmlNodeListOGCWFS.item(iOGCWFS));
                                                                OGCWFSDataTables.add(new ArrayList<>());
                                                                //int iOGCWFS1 = iOGCWFS + 1;

                                                                if (getXpathString("URI",XmlCurrentOGCWFSTable) != null)
                                                                {
                                                                    String dataCaption = getXpathString("@caption", XmlCurrentOGCWFSTable);
                                                                    String dataDescription = "";
                                                                    if (getXpathString("@description", XmlCurrentOGCWFSTable) != null) {
                                                                        dataDescription = getXpathString("@description", XmlCurrentOGCWFSTable);
                                                                    }
                                                                    String dataMessage = getXpathString("@nodata",XmlCurrentOGCWFSTable);
                                                                    //String dataConnection = getXpathString("SQL/@connection",XmlCurrentOGCWFSTable);
                                                                    String dataColWidths = getXpathString("URI/@colwidths",XmlCurrentOGCWFSTable);
                                                                    String dataURL = getXpathString("URI",XmlCurrentOGCWFSTable);
                                                                    dataURL = dataURL.replace("@featurekey", keyEncode4URL(featKey));
                                                                    dataURL = dataURL.replace("@databasekey", keyEncode4URL(dataKey));
                                                                    dataURL = dataURL.replace("@referencekey", keyEncode4URL(refKey));


                                                                    String propertyName = getQueryStringPropertyName(dataURL);

                                                                    // Initialise ogr datasource
                                                                    DataSource dsOgr;
                                                                    // Initialise ogr layer
                                                                    Layer layer1;
                                                                    if(isURLReachable(dataURL)) {
                                                                        ogr.RegisterAll();
                                                                        if (dataURL.startsWith("https")) {
                                                                            if (Objects.equals(gdal.GetConfigOption("GDAL_HTTP_UNSAFESSL", "NO"), "NO")) {
                                                                                gdal.SetConfigOption("GDAL_HTTP_UNSAFESSL", "YES");
                                                                            }
                                                                        }
                                                                        dsOgr = ogr.Open(dataURL, 0);
                                                                        layer1 = dsOgr.GetLayerByIndex(0);

                                                                        if (!Objects.equals(propertyName, "")) {
                                                                            String FeatureSQL = "SELECT \"" + propertyName.replace(",", "\", \"") + "\" FROM \"" + layer1.GetName() + "\"";
                                                                            layer1 = dsOgr.ExecuteSQL(FeatureSQL, null, "SQLITE");
                                                                        }

                                                                        if (layer1 != null) {

                                                                            FeatureDefn layerDefinition = layer1.GetLayerDefn();
                                                                            int fieldCount = layerDefinition.GetFieldCount();



                                                                            // We add +1 if we want to include the Geometry type/WKT as a column
                                                                            PdfPTable table = new PdfPTable(fieldCount);
                                                                            table.setWidthPercentage(100);

                                                                            // Add Headers from OGR Field Definitions
                                                                            for (int i = 0; i < fieldCount; i++) {
                                                                                FieldDefn fieldDefn = layerDefinition.GetFieldDefn(i);
                                                                                PdfPCell header = new PdfPCell(new Phrase(fieldDefn.GetName()));
                                                                                table.addCell(header);
                                                                            }

                                                                            // Populate Rows from Features
                                                                            layer1.ResetReading();
                                                                            Feature feature;
                                                                            while ((feature = layer1.GetNextFeature()) != null) {
                                                                                for (int i = 0; i < fieldCount; i++) {
                                                                                    // Check field type and handle nulls
                                                                                    if (feature.IsFieldSet(i)) {
                                                                                        table.addCell(feature.GetFieldAsString(i));
                                                                                    } else {
                                                                                        table.addCell("");
                                                                                    }
                                                                                }
                                                                                feature.delete(); // Important: Manually free native memory
                                                                            }

                                                                            // Data Title Table
                                                                            OGCWFSDataTables.get(iOGCWFS).add(getDataTableSingleCell(dataCaption, titleFont, titleColor, titleBorderColor, titleBorderWidth));

                                                                            if(table.getRows().isEmpty()) {
                                                                                // No Data Message Table
                                                                                OGCWFSDataTables.get(iOGCWFS).add(getDataTableSingleCell(dataMessage, descriptionFont, descriptionColor, descriptionBorderColor, descriptionBorderWidth));
                                                                            } else {
                                                                                // Data Description Table
                                                                                PdfPTable descriptionTable = getDataTableSingleCell(dataDescription, descriptionFont, descriptionColor, descriptionBorderColor, descriptionBorderWidth);
                                                                                if (descriptionTable.size() > 0) {
                                                                                    OGCWFSDataTables.get(iOGCWFS).add(descriptionTable);
                                                                                }
                                                                                // Data Table
                                                                                OGCWFSDataTables.get(iOGCWFS).add(getDataTableFromRawOGCWFS(table,dataColWidths, headerFont, headerColor, headerBorderColor, headerBorderWidth, cellFont, cellColor, cellBorderColor, cellBorderWidth, alternateCellColor, alternateCellBorderColor, alternateCellBorderWidth));
                                                                            }
                                                                            // Cleanup
                                                                            dsOgr.delete();
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                            drawNestedTables(pdfwriter, document,OGCWFSDataTables,Float.parseFloat(DataTableX),Float.parseFloat(DataTableY),Float.parseFloat(DataTableWidth));
                                                        }
                                                    }
                                                }
                                                break;
                                            default:
                                                break;
                                        }
                                    }

                                }
                            }
                        }


                    } catch (IOException e) {
                        logger.error("Error reading file: {}", e.getMessage());
                    } catch (XPathExpressionException e) {
                        logger.error("XPath Expression Error: {}", e.getMessage());
                    } catch (Exception e) {
                        logger.error("Unable to generate your report.");
                        logger.error("Config File: {}", myConfigFilePath);
                        logger.error("Error: {}", e.getMessage());
                        logger.error("Cause: {}", String.valueOf(e.getCause()));
                        logger.error("Stacktrace: {}", Arrays.toString(e.getStackTrace()));
                    }
                }
                p = 99; //finished adding content
            } catch (DocumentException e) {
                p = -1;
                //e.printStackTrace();
                logger.error("Document exception: {}", e.getMessage());
            } catch (Exception e) {
                p = -1;
                logger.error("Unable to finish your report.");
                logger.error("Error: {}", e.getMessage());
            }
            logger.info("Finished assembling PDF");
        } catch (Exception e) {
            task.error = e.getMessage();
            try {
                if(task.tempFile != null) {
                    Files.deleteIfExists(task.tempFile);
                }
            } catch (IOException ignored) {}
        } finally {
            logger.info("Assembly Done.");
        }
    }

    private CoordinateTransformation getCoordinateTransformation(String s_epsgRaw, String t_epsgRaw) {
        SpatialReference s_srs = new SpatialReference("");
        s_srs.ImportFromEPSG(Integer.parseInt(s_epsgRaw));
        s_srs.SetAxisMappingStrategy(osr.OAMS_TRADITIONAL_GIS_ORDER);  // Fix for TransformPoint method x and y flipped using GDAL 3.0.4 compared to GDAL 2.4
        SpatialReference t_srs = new SpatialReference("");
        t_srs.ImportFromEPSG(Integer.parseInt(t_epsgRaw));
        t_srs.SetAxisMappingStrategy(osr.OAMS_TRADITIONAL_GIS_ORDER);  // Fix for TransformPoint method x and y flipped using GDAL 3.0.4 compared to GDAL 2.4
        return new CoordinateTransformation(s_srs, t_srs);
    }

    private int getMapFeatureTextFontStyleValue(String fontStyle) {
        int fontStyleValue = 0; //regular
        if (Objects.equals(fontStyle.toLowerCase(), "italic")) {
            //Italic;
            fontStyleValue = Font.ITALIC;
        }
        if (Objects.equals(fontStyle.toLowerCase(), "bold")) {
            //Bold;
            fontStyleValue = Font.BOLD;
        }
        if (Objects.equals(fontStyle.toLowerCase(), "bolditalic")) {
            //Bold | Italic;
            fontStyleValue = Font.BOLDITALIC;
        }
        return fontStyleValue;
    }

    private void handleForeignPage(Node pageNode, PdfTask parentTask, String sessionId, Document document, PdfWriter pdfwriter, int depth) throws Exception {
        /*
        <Pages>
            <Page type="foreign">
                <ForeignPages>
                    <ForeignPage type="internal" report="SubReportName" importpage="all">
                        <Param name="featkey">@featurekey</Param>
                    </ForeignPage>
                </ForeignPages>
            </Page>
        </Pages>
         */


        NodeList foreignItems = getXpathNodeList(".//ForeignPage", pageNode);

        for (int j = 0; j < foreignItems.getLength(); j++) {
            Node item = foreignItems.item(j);
            String type = getXpathString("@type", item);
            String foreignDocImportPage = getXpathString("@importpage", item);

            if ("internal".equalsIgnoreCase(type)) {
                // RECURSION POINT: Generate sub-report in memory
                String subReportName = getXpathString("@report", item);
                logger.info("Internal Request started for FeatKey: {} Subreport: {}", parentTask.featureKey, subReportName);
                PdfTask subTask = new PdfTask(subReportName, parentTask.featureKey, parentTask.databaseKey, parentTask.referenceKey, parentTask.scaleRawValue, parentTask.s_epsgRawValue, parentTask.t_epsgRawValue, parentTask.xRawValue, parentTask.yRawValue);
                subTask.tempFile = Files.createTempFile("subreport_", ".pdf");
                subTasks.put(sessionId, subTask);
                logger.info(subTask.tempFile.toString());

                generateSubReport(subTask, sessionId, depth + 1);

                if (subTask.isDone && Files.size(subTask.tempFile) >= 0) {
                    PdfReader reader = new PdfReader(subTask.tempFile.toString());
                    drawPdfPages(reader, foreignDocImportPage, document, pdfwriter);
                }
            } else {
                // Standard File Path
                String foreignDoc = item.getTextContent();
                if (new File(foreignDoc).exists()) {
                    drawPdfPages(new PdfReader(foreignDoc), foreignDocImportPage, document, pdfwriter);
                }
            }
        }
    }

    private void generateSubReport(PdfTask subTask, String sessionId, int depth) throws IOException {
        OutputStream os = Files.newOutputStream(subTask.tempFile);
        try {
            Document subDoc = new Document();
            PdfWriter subWriter = PdfWriter.getInstance(subDoc, os);
            subDoc.open();

            assemblePdf(subTask, sessionId, subDoc, subWriter, depth);

            subDoc.close();
            os.close();
            os = null;
        } catch (Exception e) {
            logger.error("Sub-report failed");
            subTask.error = e.getMessage();
        } finally {
            if (os != null) try { os.close(); } catch (IOException ignored) {}
            subTask.isDone = true;
            logger.info("Subtask Done.");
        }

    }

    private void drawPdfPages(PdfReader reader, String pagesToImport, Document document, PdfWriter pdfwriter) {
        try {
            int total = reader.getNumberOfPages();
            PdfContentByte cb = pdfwriter.getDirectContent();
            for (int i = 1; i <= total; i++) {
                // Simple logic: if 'all' or specific page number matches
                document.setPageSize(reader.getPageSizeWithRotation(i));
                document.newPage();
                PdfImportedPage page = pdfwriter.getImportedPage(reader, i);
                cb.addTemplate(page, 0, 0);
                cb.sanityCheck();
            }
            reader.close();
        } catch (Exception e) {
            logger.error("Error drawing foreign pages", e);
        }
    }

    private void handleDownload(HttpServletRequest req, HttpServletResponse resp) throws IOException {
        logger.info("Handling download");
        String sessionId = req.getSession().getId();
        PdfTask task = mainTasks.remove(sessionId);

        if (task != null && task.tempFile != null && Files.exists(task.tempFile)) {
            resp.setContentType("application/pdf");
            resp.setHeader("Content-Disposition", "inline; filename=\"georeport_"+ task.reportType+ "_" + task.featureKey.replace("/", "_") + ".pdf\"");
            resp.setContentLengthLong(Files.size(task.tempFile));

            // Efficient transfer from Disk to Socket
            Files.copy(task.tempFile, resp.getOutputStream());
            Files.deleteIfExists(task.tempFile);
            logger.info("Downloaded");
        } else {
            logger.info("The report has expired or failed to generate.  Running download error handler.");
            handleDownloadError(req, resp);
        }
    }

    public void handleDownloadError(HttpServletRequest req, HttpServletResponse resp) throws IOException {
        String referer = req.getHeader("Referer");
        String serverName = req.getServerName(); // e.g., "example.com"
        String redirectUrl = ""; // Fallback path

        if (referer != null) {
            try {
                java.net.URL url = new java.net.URL(referer);
                // Check if the referer host matches our server host
                if (url.getHost().equalsIgnoreCase(serverName)) {
                    redirectUrl = referer;
                    logger.debug("Redirecting to Referer: " + redirectUrl);
                }
            } catch (java.net.MalformedURLException e) {
                // Invalid URL format, stick with fallback
                logger.debug("Invalid URL format.  Redirecting to home: " + redirectUrl);
            }
        }

        resp.sendRedirect(redirectUrl);
    }

    private void cleanupAbandonedFiles() {
        logger.info("Cleaning up temporary PDF files.");

        Properties fileConfigs = new Properties();
        try {
            fileConfigs.load(new FileInputStream(configFilePath));
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        long limit = System.currentTimeMillis() - TimeUnit.MINUTES.toMillis(Integer.parseInt(fileConfigs.getProperty("file.tempFileLifeMinutes")));

        // Filter for PDF files specifically
        Predicate<Path> isPdf = path -> path.getFileName().toString().toLowerCase().endsWith(".pdf");

        // 1. Cleanup expired entries from active maps
        Predicate<Map.Entry<String, PdfTask>> isExpired = entry -> {
            Path path = entry.getValue().tempFile;
            try {
                if (path != null && isPdf.test(path) && Files.getLastModifiedTime(path).toMillis() < limit) {
                    Files.deleteIfExists(path);
                    return true;
                }
            } catch (IOException ignored) {}
            return false;
        };

        mainTasks.entrySet().removeIf(isExpired);
        subTasks.entrySet().removeIf(isExpired);

        // 2. Scan directory for "Orphaned" PDF files
        Path tempDirectoryPath = Paths.get(System.getProperty("java.io.tmpdir"));

        try (Stream<Path> files = Files.list(tempDirectoryPath)) {
            // Collect active paths into a Set for fast lookup
            Set<Path> activeFiles = new HashSet<>();
            mainTasks.values().forEach(t -> { if(t.tempFile != null) activeFiles.add(t.tempFile); });
            subTasks.values().forEach(t -> { if(t.tempFile != null) activeFiles.add(t.tempFile); });

            files.filter(isPdf) // Ensure we only touch .pdf files
                 .filter(path -> !activeFiles.contains(path))
                 .filter(path -> {
                     try {
                         return Files.getLastModifiedTime(path).toMillis() < limit;
                     } catch (IOException e) { return false; }
                 })
                 .forEach(path -> {
                     try {
                         Files.deleteIfExists(path);
                         logger.debug("Deleted orphaned PDF: " + path.getFileName());
                     } catch (IOException ignored) {}
                 });

        } catch (IOException e) {
            logger.error("Failed to scan directory for PDF cleanup", e);
        }
    }

    private void showUi(HttpServletRequest req, HttpServletResponse resp) throws IOException {
        getURLParameters(req);
        if (dataKey == null){ dataKey = "";}
        if (refKey == null){ refKey = "";}
        if (scaleRaw == null){ scaleRaw = "";}
        if (s_epsgRaw == null){ s_epsgRaw = "";}
        if (t_epsgRaw == null){ t_epsgRaw = "";}
        if (xRaw == null){ xRaw = "";}
        if (yRaw == null){ yRaw = "";}

        resp.setContentType("text/html");
        resp.getWriter().println("""
            <html>
            <head>
                <title>GeoReports</title>
                <link rel="stylesheet" type="text/css" href="georeports.css">
                <style>
                    #box { border: 2px solid #000; height: 25px; border-radius: 4px; }
                    #bar { width: 0%; height: 100%; background: #2ecc71; transition: width 0.3s; }
                </style>
            </head>
            <body>
                <div class="msg_content">
                <h2>Generating Report</h2>""");
        resp.getWriter().println("""
                        <div id="box" style="margin-top:15px;">
                        <div id="bar"></div></div>
                <p id="stat"></p>
                <script>
                    function run(report, featKey, dataKey, refKey, scaleRaw, s_epsgRaw, t_epsgRaw, xRaw, yRaw) {
                        const bar = document.getElementById('bar');
                        const stat = document.getElementById('stat');
                        const source = new EventSource(`georeport/progress?report=${report}&featkey=${featKey}&dataKey=${dataKey}&refKey=${refKey}&scale=${scaleRaw}&s_epsg=${s_epsgRaw}&t_epsg=${t_epsgRaw}&x=${xRaw}&y=${yRaw}`);

                        source.onmessage = (e) => {
                            if (e.data === 'complete') {
                                source.close();
                                stat.innerText = "Report Completed!  Downloading...";
                                window.location.href = 'georeport/download';
                            } else {
                                bar.style.width = e.data + '%';
                                stat.innerText = "Processing: " + e.data + "%";
                            }
                        };
                        source.addEventListener('error', () => {
                            source.close();
                            stat.innerText = "Server Error during generation.";
                        });
                    }
                """);
        resp.getWriter().println("window.addEventListener('load', run('" + report + "', '" + featKey + "', '" + dataKey + "', '" + refKey + "', '" + scaleRaw + "', '" + s_epsgRaw + "', '" + t_epsgRaw + "', '" + xRaw + "', '" + yRaw + "'));");
        resp.getWriter().println("""
                </script>
                </div>
            </body></html>
            """);

    }

    @Override
    public void destroy() {
        logger.info("Shutting down GeoReports.");
        executor.shutdownNow();
        janitor.shutdownNow();
    }


    private void getURLParameters(HttpServletRequest req) {
        // required URL params
        logger.info("URL Parameters: " + req.getQueryString());
        try {
            if(req.getParameter("report").matches("[A-z0-9-_./]+")){
                report = req.getParameter("report");
            }
            if(req.getParameter("featkey").matches("[0-9A-z\\-._* /]+")){
                featKey = req.getParameter("featkey");
            }
        } catch (PatternSyntaxException | NullPointerException e) {
            logger.error(e.getMessage());
        }

        //optional URL Params
        try {
            if(req.getParameter("datakey").matches("[0-9A-z\\-._* /]+")){
                dataKey = req.getParameter("datakey");
            }
        } catch (PatternSyntaxException e) {
            logger.error(e.getMessage());
        } catch (NullPointerException e) {
            logger.debug("datakey is null");
        }
        try {
            if(req.getParameter("refkey").matches("[0-9A-z\\-._* /]+")){
                refKey = req.getParameter("refkey");
            }
        } catch (PatternSyntaxException e) {
            logger.error(e.getMessage());
        } catch (NullPointerException e) {
            logger.debug("refkey is null");
        }

        // scaleRaw
        try {
            if(req.getParameter("scale").matches("[0-9]+|auto")){
                scaleRaw = req.getParameter("scale");
            }
        } catch (PatternSyntaxException e) {
            logger.error(e.getMessage());
        } catch (NullPointerException e) {
            logger.debug("scale is null");
        }
        // s_epsgRaw
        try {
            if(req.getParameter("s_epsg").matches("[0-9]{4}")){
                s_epsgRaw = req.getParameter("s_epsg");
            }
        } catch (PatternSyntaxException e) {
            logger.error(e.getMessage());
        } catch (NullPointerException e) {
            logger.debug("s_epsg is null");
        }
        // t_epsgRaw
        try {
            if(req.getParameter("t_epsg").matches("[0-9]{4}")){
                t_epsgRaw = req.getParameter("t_epsg");
            }
        } catch (PatternSyntaxException e) {
            logger.error(e.getMessage());
        } catch (NullPointerException e) {
            logger.debug("t_epsg is null");
        }
        // xRaw
        try {
            if(req.getParameter("x").matches("[.0-9]+")){
                xRaw = req.getParameter("x");
            }
        } catch (PatternSyntaxException e) {
            logger.error(e.getMessage());
        } catch (NullPointerException e) {
            logger.debug("x is null");
        }
        // yRaw
        try {
            if(req.getParameter("y").matches("[-.0-9]+")){
                yRaw = req.getParameter("y");
            }
        } catch (PatternSyntaxException e) {
            logger.error(e.getMessage());
        } catch (NullPointerException e) {
            logger.debug("y is null");
        }
    }

    private void setLabelVariables(Object currentLabel) throws XPathExpressionException {
        String[] splitResult;
        //int textAlignment = 0; //default to left aligned
        //Label position
        if (getXpathString("@position", currentLabel) != null) {
            String labelPosition = getXpathString("@position", currentLabel);
            splitResult = labelPosition.split(",");
            LabelPositionX = Float.parseFloat(splitResult[0]);
            LabelPositionY = Float.parseFloat(splitResult[1]);
        }
        //Label size
        if (getXpathString("@size", currentLabel) != null) {
            String labelSize = getXpathString("@size", currentLabel);
            splitResult = labelSize.split(",");
            LabelWidth = Float.parseFloat(splitResult[0]);
            LabelHeight = Float.parseFloat(splitResult[1]);
        }
        //horizontal alignment
        if (getXpathString("@halign", currentLabel) != null) {
            switch (getXpathString("@halign", currentLabel))
            {
                case "4":
                    textAlignment = ALIGN_CENTER;
                    break;
                case "2":
                    textAlignment = ALIGN_RIGHT;
                    break;
                case "8":
                    textAlignment = 3;
                    break;
                default:
                    textAlignment = ALIGN_LEFT;
                    break;
            }
        }
    }

    private void drawMapFeatureLine(Document document, PdfContentByte cb, ArrayList<Point2D> featurePoints, Color borderColor, float borderWidth) {
        cb.resetRGBColorStroke();
        cb.saveState();
        //draw clipping rectangle based on map image
        cb.rectangle(millimetersToPoints(Float.parseFloat(MapImageX)),getTopY(document,millimetersToPoints(Float.parseFloat(MapImageY)))-millimetersToPoints(Float.parseFloat(MapImageHeight)),millimetersToPoints(Float.parseFloat(MapImageWidth)), millimetersToPoints(Float.parseFloat(MapImageHeight)));
        cb.clip();
        cb.newPath();
        cb.setRGBColorStroke(borderColor.getRed(),borderColor.getGreen(),borderColor.getBlue(),borderColor.getAlpha());
        for (int i = 0; i < featurePoints.size(); i++) {
            if (i == 0) {
                cb.moveTo((float) featurePoints.get(i).getX(), (float) featurePoints.get(i).getY());
            }
            cb.lineTo((float) featurePoints.get(i).getX(),  (float) featurePoints.get(i).getY());
        }
        cb.setLineWidth(borderWidth);
        cb.stroke();
        cb.restoreState();
        cb.sanityCheck();
    }

    private void drawMapFeaturePolygon(Document document, PdfContentByte cb, ArrayList<Point2D> featurePoints, Color backgroundColor, Color borderColor, float borderWidth) {
        cb.resetRGBColorFill();
        cb.resetRGBColorStroke();
        cb.saveState();
        //draw clipping rectangle based on map image
        cb.rectangle(millimetersToPoints(Float.parseFloat(MapImageX)),getTopY(document,millimetersToPoints(Float.parseFloat(MapImageY)))-millimetersToPoints(Float.parseFloat(MapImageHeight)),millimetersToPoints(Float.parseFloat(MapImageWidth)), millimetersToPoints(Float.parseFloat(MapImageHeight)));
        cb.clip();
        cb.newPath();
        cb.setRGBColorStroke(borderColor.getRed(),borderColor.getGreen(),borderColor.getBlue(),borderColor.getAlpha());
        cb.setRGBColorFill(backgroundColor.getRed(),backgroundColor.getGreen(),backgroundColor.getBlue(),backgroundColor.getAlpha());
        for (int i = 0; i < featurePoints.size(); i++) {
            if (i == 0) {
                cb.moveTo((float) featurePoints.get(i).getX(), (float) featurePoints.get(i).getY());
            }
            cb.lineTo((float) featurePoints.get(i).getX(),  (float) featurePoints.get(i).getY());
        }
        cb.setLineWidth(borderWidth);
        //cb.closePathStroke();
        cb.closePathFillStroke();
        cb.restoreState();
        cb.sanityCheck();
    }

    private void drawMapFeatureEllipseFromCenter(Document document, PdfContentByte cb, Point2D centerPoint, float width, float height, Color backgroundColor, Color borderColor, float borderWidth) {
        cb.resetRGBColorFill();
        cb.resetRGBColorStroke();
        cb.saveState();
        //draw clipping rectangle based on map image
        cb.rectangle(millimetersToPoints(Float.parseFloat(MapImageX)),getTopY(document,millimetersToPoints(Float.parseFloat(MapImageY)))-millimetersToPoints(Float.parseFloat(MapImageHeight)),millimetersToPoints(Float.parseFloat(MapImageWidth)), millimetersToPoints(Float.parseFloat(MapImageHeight)));
        cb.clip();
        cb.newPath();
        cb.setRGBColorStroke(borderColor.getRed(),borderColor.getGreen(),borderColor.getBlue(),borderColor.getAlpha());
        cb.setRGBColorFill(backgroundColor.getRed(),backgroundColor.getGreen(),backgroundColor.getBlue(),backgroundColor.getAlpha());
        // Calculate the bounding box corners for the ellipse
        float x1 = (float) (centerPoint.getX() - (width / 2));
        float y1 = (float) (centerPoint.getY() - (height / 2));
        float x2 = (float) (centerPoint.getX() + (width / 2));
        float y2 = (float) (centerPoint.getY() + (height / 2));
        cb.ellipse(x1,y1,x2,y2);
        cb.setLineWidth(borderWidth);
        //cb.closePathStroke();
        cb.closePathFillStroke();
        cb.restoreState();
        cb.sanityCheck();
    }

    private void drawMapFeatureRectangleFromCenter(Document document, PdfContentByte cb, Point2D centerPoint, float width, float height, Color backgroundColor, Color borderColor, float borderWidth) {
        cb.resetRGBColorFill();
        cb.resetRGBColorStroke();
        cb.saveState();
        //draw clipping rectangle based on map image
        cb.rectangle(millimetersToPoints(Float.parseFloat(MapImageX)),getTopY(document,millimetersToPoints(Float.parseFloat(MapImageY)))-millimetersToPoints(Float.parseFloat(MapImageHeight)),millimetersToPoints(Float.parseFloat(MapImageWidth)), millimetersToPoints(Float.parseFloat(MapImageHeight)));
        cb.clip();
        cb.newPath();
        cb.setRGBColorStroke(borderColor.getRed(),borderColor.getGreen(),borderColor.getBlue(),borderColor.getAlpha());
        cb.setRGBColorFill(backgroundColor.getRed(),backgroundColor.getGreen(),backgroundColor.getBlue(),backgroundColor.getAlpha());
        float x1 = (float) (centerPoint.getX() - (width / 2));
        float y1 = (float) (centerPoint.getY() - (height / 2));
        cb.rectangle(x1,y1,width,height);
        cb.setLineWidth(borderWidth);
        //cb.closePathStroke();
        cb.closePathFillStroke();
        cb.restoreState();
        cb.sanityCheck();
    }

    private void drawMapFeatureText(Document document, PdfContentByte cb, Point2D centerPoint, String text, Font font, int textAlignment, float rotation) {
        cb.saveState();
        //draw clipping rectangle based on map image
        cb.rectangle(millimetersToPoints(Float.parseFloat(MapImageX)),getTopY(document,millimetersToPoints(Float.parseFloat(MapImageY)))-millimetersToPoints(Float.parseFloat(MapImageHeight)),millimetersToPoints(Float.parseFloat(MapImageWidth)), millimetersToPoints(Float.parseFloat(MapImageHeight)));
        cb.clip();
        cb.newPath();
        cb.beginText();
        BaseFont bf = font.getBaseFont();
        cb.setFontAndSize(bf, font.getSize());
        cb.setColorFill(font.getColor());
        cb.showTextAligned(textAlignment,text, (float) centerPoint.getX(), (float) (centerPoint.getY() - (font.getSize()/2)), rotation);
        cb.endText();
        cb.restoreState();
        cb.sanityCheck();
    }

    private void drawMapFeatureImage(String imageURL, Point2D centerPoint, String imageScaleFactor, Document document) throws IOException {
        if (!Objects.equals(imageURL, "")) {
            URL url = new URL(imageURL);
            InputStream in = url.openStream();
            byte[] imageBytes = in.readAllBytes(); // Read all bytes from the stream
            in.close();
            Image image = Image.getInstance(imageBytes);
            float maxWidth = image.getWidth() * Float.parseFloat(imageScaleFactor); // Maximum width of the image
            float maxHeight = image.getHeight() * Float.parseFloat(imageScaleFactor); // Maximum height of the image
            image.setAbsolutePosition((float) centerPoint.getX(), (float) centerPoint.getY());
            image.scaleToFit(maxWidth, maxHeight); // Scales the image to fit within the max dimensions while maintaining aspect ratio
            document.add(image);
        }
    }


    private String getOGRConnectionString(String ScaleFeatureSQLConnectionName) throws IOException {
        String ScaleFeatureSQLConnection;
        Properties dbConfigs = new Properties();
        dbConfigs.load(new FileInputStream(dbConfigFilePath));

        // 2. Get connection details for the specified database
        String urlKey = ScaleFeatureSQLConnectionName + ".url";
        String userKey = ScaleFeatureSQLConnectionName + ".user";
        String passwordKey = ScaleFeatureSQLConnectionName + ".password";
        String driverKey = ScaleFeatureSQLConnectionName + ".driver";

        String dbURL = dbConfigs.getProperty(urlKey);
        String dbUser = dbConfigs.getProperty(userKey);
        String dbPassword = dbConfigs.getProperty(passwordKey);
        String dbDriver = dbConfigs.getProperty(driverKey);

        ScaleFeatureSQLConnection = dbDriver + ":" + dbURL + " user=" + dbUser + " password=" + dbPassword;
        return ScaleFeatureSQLConnection;
    }

    private ArrayList<Point2D> getMapFeatureGeometryPoints(Geometry FeatureGeometry,
                                                         String MapImageX, String MapImageY, String MapExtentMinX, String MapExtentMaxY,
                                                         String MapImageNeatScale, Document document){
        ArrayList<Point2D> featurePoints = new ArrayList<>();
        for (var pointIndex = 0; pointIndex < FeatureGeometry.GetPointCount(); pointIndex++)
        {
            double[] pointCoordinates = new double[3];
            FeatureGeometry.GetPoint(pointIndex, pointCoordinates);
            double MapFeatureX = pointCoordinates[0];
            double MapFeatureY = pointCoordinates[1];
            float PageFeatureNodeX = (float) (Float.parseFloat(MapImageX) + (((MapFeatureX - Float.parseFloat(MapExtentMinX)) * 1000) / Float.parseFloat(MapImageNeatScale)));
            float PageFeatureNodeY = (float) (Float.parseFloat(MapImageY) - (((MapFeatureY - Float.parseFloat(MapExtentMaxY)) * 1000) / Float.parseFloat(MapImageNeatScale)));
            Point2D p = new Point2D.Float();
            p.setLocation(millimetersToPoints(PageFeatureNodeX),getTopY(document,millimetersToPoints(PageFeatureNodeY)));
            featurePoints.add(p);
        }
        return featurePoints;
    }

    private PdfPTable getDataTableFromResultSet(ResultSetMetaData metadata, String dataColWidths, Font headerFont, Color headerColor, Color headerBorderColor, float headerBorderWidth, ResultSet rs, Font cellFont, Color cellColor, Color cellBorderColor, float cellBorderWidth, Color alternateCellColor, Color alternateCellBorderColor, float alternateCellBorderWidth) throws SQLException {
        int columnCount = metadata.getColumnCount();
        PdfPTable datatable = new PdfPTable(columnCount);
        int[] columnWidths = StreamSplitStringToIntArray(dataColWidths);
        if (columnCount == columnWidths.length) {
            datatable.setWidths(columnWidths);
        }
        datatable.setWidthPercentage(100);
        //datatable.setSpacingBefore(5f);

        datatable.setHeaderRows(1);


        for (int i = 1; i <= columnCount; i++) {
            PdfPCell header = new PdfPCell(new Phrase(metadata.getColumnName(i), headerFont));
            header.setBackgroundColor(headerColor);
            header.setBorderColor(headerBorderColor);
            header.setBorderWidth(headerBorderWidth);
            header.setHorizontalAlignment(PdfPCell.ALIGN_LEFT);
            header.setPadding(2);
            datatable.addCell(header);
        }

        int rowCount = 0;

        while (rs.next()) {
            rowCount++;
            for (int i = 1; i <= columnCount; i++) {
                Object value = rs.getObject(i);
                PdfPCell cell = new PdfPCell(new Phrase(value != null ? value.toString() : "", cellFont));

                cell.setBackgroundColor(cellColor);
                cell.setBorderColor(cellBorderColor);
                cell.setBorderWidth(cellBorderWidth);

                // Zebra Striping logic
                if (rowCount % 2 == 0) {
                    cell.setBackgroundColor(alternateCellColor);
                    cell.setBorderColor(alternateCellBorderColor);
                    cell.setBorderWidth(alternateCellBorderWidth);
                }

                cell.setPadding(2);

                datatable.addCell(cell);
            }
        }

        return datatable;
    }

    private PdfPTable getDataTableFromRawOGCWFS(PdfPTable rawTable, String dataColWidths, Font headerFont, Color headerColor, Color headerBorderColor, float headerBorderWidth, Font cellFont, Color cellColor, Color cellBorderColor, float cellBorderWidth, Color alternateCellColor, Color alternateCellBorderColor, float alternateCellBorderWidth)  {
        int columnCount =  rawTable.getNumberOfColumns();


        PdfPTable datatable = new PdfPTable(columnCount);
        int[] columnWidths = StreamSplitStringToIntArray(dataColWidths);



        if (columnCount == columnWidths.length) {
            datatable.setWidths(columnWidths);
        }
        datatable.setWidthPercentage(100);
        //datatable.setSpacingBefore(5f);

        ArrayList<PdfPRow> rows = rawTable.getRows(); //Get all rows from the table

        // header row
        datatable.setHeaderRows(1);
        PdfPRow headerRow = rows.get(0); //Access the first row (index 0)
        PdfPCell[] headerCells = headerRow.getCells(); //Get the cells in that row

        for (PdfPCell headerCell : headerCells) {
            PdfPCell header = new PdfPCell(new Phrase(headerCell.getPhrase().getContent(), headerFont));
            header.setBackgroundColor(headerColor);
            header.setBorderColor(headerBorderColor);
            header.setBorderWidth(headerBorderWidth);
            header.setHorizontalAlignment(PdfPCell.ALIGN_LEFT);
            header.setPadding(2);
            datatable.addCell(header);
        }

        // data rows
        for (int iRow = 1; iRow < rows.size(); iRow++) {
            PdfPRow currentRow = rows.get(iRow);
            if (currentRow == null) continue;
            PdfPCell[] cells = currentRow.getCells();
            for (PdfPCell currentCell : cells) {

                PdfPCell cell = new PdfPCell(new Phrase(currentCell.getPhrase().getContent(), cellFont));

                cell.setBackgroundColor(cellColor);
                cell.setBorderColor(cellBorderColor);
                cell.setBorderWidth(cellBorderWidth);

                // Zebra Striping logic
                if (iRow % 2 == 0) {
                    cell.setBackgroundColor(alternateCellColor);
                    cell.setBorderColor(alternateCellBorderColor);
                    cell.setBorderWidth(alternateCellBorderWidth);
                }

                cell.setPadding(2);

                datatable.addCell(cell);

            }
        }
        return datatable;
    }




    private PdfPTable getDataTableSingleCell(String cellValue, Font cellFont, Color cellColor, Color cellBorderColor, float cellBorderWidth) {
        PdfPTable table = new PdfPTable(1);
        table.setWidthPercentage(100);
        //table.setSpacingBefore(5f);
        PdfPCell cell = new PdfPCell(new Phrase(cellValue != null ? cellValue : "", cellFont));
        cell.setBackgroundColor(cellColor);
        cell.setBorderColor(cellBorderColor);
        cell.setBorderWidth(cellBorderWidth);
        //cell.setPadding(2);
        table.addCell(cell);
        return table;
    }

    /**
     * Processes a nested list of tables.
     * Each table starts exactly where the previous one finished.
     * */
    public void drawNestedTables(PdfWriter writer, Document document, ArrayList<ArrayList<PdfPTable>> tableGroups,
                                 float x, float startYFromTop, float width) throws DocumentException {

        x = millimetersToPoints(x);
        width = millimetersToPoints(width);
        startYFromTop = millimetersToPoints(startYFromTop);

        float currentYFromTop = startYFromTop;

        for (ArrayList<PdfPTable> group : tableGroups) {
            for (PdfPTable table : group) {
                // Draw the table and get the Y position where it ended
                currentYFromTop = drawTableAndReturnEnd(writer, document, table, x, currentYFromTop, width);
                // Add a small gap (e.g., 10 points) between tables
                currentYFromTop += 2;
            }
        }
    }

    private float drawTableAndReturnEnd(PdfWriter writer, Document document, PdfPTable table,
                                        float x, float yFromTop, float width) throws DocumentException {

        PdfContentByte canvas = writer.getDirectContent();
        ColumnText ct = new ColumnText(canvas);

        table.setTotalWidth(width);
        table.setLockedWidth(true);
        ct.addElement(table);

        float currentY = getTopY(document, yFromTop);
        while (true) {
            // Set the box: from current Y down to the bottom margin
            ct.setSimpleColumn(x, document.bottomMargin(), x + width, currentY);
            int status = ct.go();
            if (!ColumnText.hasMoreText(status)) {
                // Table finished on this page!
                // Return the new Y position converted back to "Top-Down"
                return document.getPageSize().getHeight() - ct.getYLine();
            }

            // Table didn't fit, move to new page
            document.newPage();
            currentY = getTopY(document, document.topMargin()); // Reset Y to top of new page
        }
    }

    private void drawRectangle(PdfContentByte cb, float x, float y, float width, float height, Color backgroundColor, Color borderColor, float borderWidth, Document document){
        //convert to pts
        x = millimetersToPoints(x);
        y = getTopY(document,millimetersToPoints(y));
        width = millimetersToPoints(width);
        height = millimetersToPoints(height);
        float bottomY = y - height;
        //float rightX = x + width;

        cb.resetRGBColorFill();
        cb.resetRGBColorStroke();
        cb.saveState();
        cb.setRGBColorStroke(borderColor.getRed(),borderColor.getGreen(),borderColor.getBlue(),borderColor.getAlpha());
        cb.setRGBColorFill(backgroundColor.getRed(),backgroundColor.getGreen(),backgroundColor.getBlue(),backgroundColor.getAlpha());
        cb.setLineWidth(borderWidth);
        // rectangle(x, y, width, height) where x,y is bottom-left
        cb.rectangle(x, bottomY, width, height);
        cb.closePathFillStroke();
        cb.restoreState();
        cb.sanityCheck();
    }


    private void drawText(PdfContentByte cb,float x,float y,float width,float height,String text,Font font,int textAlignment, boolean middle, Document document) {
        //convert to pts
        x = millimetersToPoints(x);
        y = getTopY(document,millimetersToPoints(y));
        width = millimetersToPoints(width);
        height = millimetersToPoints(height);
        float bottomY = y - height;
        float rightX = x + width;
        ColumnText ct = new ColumnText(cb);
        Paragraph p = new Paragraph(text, font);
        p.setAlignment(textAlignment);
        p.setLeading(font.getSize()+1);  //Set a fixed leading (same as font size) to remove extra vertical space
        if (middle) {
            // We simulate a run to see how much space the text takes
            ct.setSimpleColumn(p, x, bottomY, rightX, y,0, ALIGN_CENTER);
            ct.go(true); // true = simulate mode
            float textHeight = ct.getYLine(); // Get where the text ended
            float offset = (height - (y - textHeight)) / 2;
            int lines = ct.getLinesWritten();
            ct.setUseAscender(true);
            ct.setSimpleColumn(x, bottomY - (offset/lines), rightX, y - (offset/lines));
            ct.addElement(p);
            ct.go(false); // false = actually draw
        } else {
            ct.setUseAscender(true);
            ct.setSimpleColumn(x, bottomY, rightX, y);
            ct.addElement(p);
            ct.go();
        }
    }


    private void setDataStylesFromQPT(String tableName, Object object) throws XPathExpressionException, IOException {
        switch (tableName) {
            case "Title":
                if(getXpathNode("LabelFont", object) != null) {
                    titleFont = setFontStylesFromQPT(object);
                }
                if (getXpathNode("BackgroundColor", object) != null) {
                    Node nodeBackgroundColor = getXpathNode("BackgroundColor", object);
                    titleColor = getColorFromXPathNode(nodeBackgroundColor);
                }
                if (getXpathNode("FrameColor", object) != null) {
                    Node nodeFrameColor = getXpathNode("FrameColor", object);
                    titleBorderColor = getColorFromXPathNode(nodeFrameColor);
                }
                if (getXpathString("@outlineWidthM", object) != null) {
                    //outlineWidthM="0.3,mm"
                    String[] splitResult = getXpathString("@outlineWidthM", object).split(",");
                    titleBorderWidth = Float.parseFloat(splitResult[0]);
                }
                break;
            case "Description":
                if(getXpathNode("LabelFont", object) != null) {
                    descriptionFont = setFontStylesFromQPT(object);
                }
                if (getXpathNode("BackgroundColor", object) != null) {
                    Node nodeBackgroundColor = getXpathNode("BackgroundColor", object);
                    descriptionColor = getColorFromXPathNode(nodeBackgroundColor);
                }
                if (getXpathNode("FrameColor", object) != null) {
                    Node nodeFrameColor = getXpathNode("FrameColor", object);
                    descriptionBorderColor = getColorFromXPathNode(nodeFrameColor);
                }
                if (getXpathString("@outlineWidthM", object) != null) {
                    String[] splitResult = getXpathString("@outlineWidthM", object).split(",");
                    descriptionBorderWidth = Float.parseFloat(splitResult[0]);
                }
                break;
            case "Header":
                if(getXpathNode("LabelFont", object) != null) {
                    headerFont = setFontStylesFromQPT(object);
                }
                if (getXpathNode("BackgroundColor", object) != null) {
                    Node nodeBackgroundColor = getXpathNode("BackgroundColor", object);
                    headerColor = getColorFromXPathNode(nodeBackgroundColor);
                }
                if (getXpathNode("FrameColor", object) != null) {
                    Node nodeFrameColor = getXpathNode("FrameColor", object);
                    headerBorderColor = getColorFromXPathNode(nodeFrameColor);
                }
                if (getXpathString("@outlineWidthM", object) != null) {
                    String[] splitResult = getXpathString("@outlineWidthM", object).split(",");
                    headerBorderWidth = Float.parseFloat(splitResult[0]);
                }
                break;
            case "Cell":
                if(getXpathNode("LabelFont", object) != null) {
                    cellFont = setFontStylesFromQPT(object);
                }
                if (getXpathNode("BackgroundColor", object) != null) {
                    Node nodeBackgroundColor = getXpathNode("BackgroundColor", object);
                    cellColor = getColorFromXPathNode(nodeBackgroundColor);
                }
                if (getXpathNode("FrameColor", object) != null) {
                    Node nodeFrameColor = getXpathNode("FrameColor", object);
                    cellBorderColor = getColorFromXPathNode(nodeFrameColor);
                }
                if (getXpathString("@outlineWidthM", object) != null) {
                    String[] splitResult = getXpathString("@outlineWidthM", object).split(",");
                    cellBorderWidth = Float.parseFloat(splitResult[0]);
                }
                break;
            case "CellAlternate":
                if(getXpathNode("LabelFont", object) != null) {
                    cellFont = setFontStylesFromQPT(object);
                }
                if (getXpathNode("BackgroundColor", object) != null) {
                    Node nodeBackgroundColor = getXpathNode("BackgroundColor", object);
                    alternateCellColor = getColorFromXPathNode(nodeBackgroundColor);
                }
                if (getXpathNode("FrameColor", object) != null) {
                    Node nodeFrameColor = getXpathNode("FrameColor", object);
                    alternateCellBorderColor = getColorFromXPathNode(nodeFrameColor);
                }
                if (getXpathString("@outlineWidthM", object) != null) {
                    String[] splitResult = getXpathString("@outlineWidthM", object).split(",");
                    alternateCellBorderWidth = Float.parseFloat(splitResult[0]);
                }
                break;
        }
    }

    private Font setFontStylesFromQPT(Object object) throws XPathExpressionException, IOException {
        if (getXpathNode("text-style",object) != null) {
            //New QGIS format
            //  <text-style fontItalic="0" fontFamily="Arial" forcedItalic="0" tabStopDistanceUnit="Percentage" fontWeight="75" textOrientation="horizontal" namedStyle="Bold" stretchFactor="100" capitalization="0" fontSize="9" fontStrikeout="0" fontLetterSpacing="0" textOpacity="1" previewBkgrdColor="255,255,255,255,rgb:1,1,1,1" multilineHeight="1" fontSizeUnit="Point" allowHtml="0" forcedBold="0" fontSizeMapUnitScale="3x:0,0,0,0,0,0" tabStopDistance="6" textColor="0,0,0,255,rgb:0,0,0,1" blendMode="0" multilineHeightUnit="Percentage" fontWordSpacing="0" tabStopDistanceMapUnitScale="3x:0,0,0,0,0,0" fontKerning="1" fontUnderline="0">

            String qptFontFamily = getXpathString("text-style/@fontFamily", object);
            String qptFontWeight = getXpathString("text-style/@fontWeight", object);
            String qptFontItalic = getXpathString("text-style/@fontItalic", object);
            int fontStyle = getFontStyle(qptFontWeight,qptFontItalic);
            String qptFontSize = getXpathString("text-style/@fontSize", object);
            float fontSize = Float.parseFloat(qptFontSize);

            String ttf = "/usr/share/fonts/truetype/msttcorefonts/" + qptFontFamily + ".ttf";
            Path linuxttfpath = Paths.get(ttf);
            Font font;
            // check if file exists in os
            if (Files.exists(linuxttfpath)) {
                // Create the BaseFont (Identity-H handles Unicode encoding)
                BaseFont bf = BaseFont.createFont(ttf, BaseFont.IDENTITY_H, BaseFont.EMBEDDED);
                font = new Font(bf, fontSize);
            } else {
                if (System.getProperty("os.name").toLowerCase().contains("linux")) {
                    //linux
                    //unknown ttf so use default
                    font = new Font(Font.HELVETICA, fontSize);
                } else {
                    ttf = qptFontFamily.toLowerCase() + ".ttf";
                    BaseFont bf = BaseFont.createFont(ttf, BaseFont.IDENTITY_H, BaseFont.EMBEDDED);
                    font = new Font(bf, fontSize);
                }
            }
            font.setStyle(fontStyle);
            if (getXpathString("text-style/@textColor", object) != null) {
                String qptTextColor= getXpathString("text-style/@textColor", object);
                String[] splitResult;
                splitResult = qptTextColor.split(",");
                int r = Integer.parseInt(splitResult[0]);
                int g = Integer.parseInt(splitResult[1]);
                int b = Integer.parseInt(splitResult[2]);
                font.setColor(new Color(r, g, b));
            }
            return font;
        } else {
            //old QGIS format
            //Font description. e.g. Arial,14,-1,5,75,0,0,0,0,0
            String dataTableFontDescription = getXpathString("LabelFont/@description", object);
            String[] splitResult;
            splitResult = dataTableFontDescription.split(",");

            String dataTableFontName = splitResult[0];
            float fontSize = Float.parseFloat(splitResult[1]);
            int fontStyle = getFontStyle(splitResult);

            String ttf = "/usr/share/fonts/truetype/msttcorefonts/" + dataTableFontName + ".ttf";
            Path linuxttfpath = Paths.get(ttf);
            Font font;
            // check if file exists in os
            if (Files.exists(linuxttfpath)) {
                // Create the BaseFont (Identity-H handles Unicode encoding)
                BaseFont bf = BaseFont.createFont(ttf, BaseFont.IDENTITY_H, BaseFont.EMBEDDED);
                font = new Font(bf, fontSize);
            } else {
                if (System.getProperty("os.name").toLowerCase().contains("linux")) {
                    //linux
                    //unknown ttf so use default
                    font = new Font(Font.HELVETICA, fontSize);
                } else {
                    ttf = dataTableFontName.toLowerCase() + ".ttf";
                    BaseFont bf = BaseFont.createFont(ttf, BaseFont.IDENTITY_H, BaseFont.EMBEDDED);
                    font = new Font(bf, fontSize);
                }
            }
            font.setStyle(fontStyle);
            if (getXpathString("FontColor", object) != null) {
                Node nodeFontColor = getXpathNode("FontColor", object);
                font.setColor(getRGBColorFromXPathNode(nodeFontColor));
            }
            return font;
        }


    }

    private int getFontStyle(String fontWeight, String fontItalic) {
        int fontStyle = 0; //default to regular
        if (Objects.equals(fontWeight, "50") && Objects.equals(fontItalic, "1")) {
            //Italic;
            fontStyle = Font.ITALIC;
        }
        if (Objects.equals(fontWeight, "75") && Objects.equals(fontItalic, "0")) {
            //Bold;
            fontStyle = Font.BOLD;
        }
        if (Objects.equals(fontWeight, "75") && Objects.equals(fontItalic, "1")) {
            //Bold | Italic;
            fontStyle = Font.BOLDITALIC;
        }
        return fontStyle;
    }

    private int getFontStyle(String[] splitResult) {
        int fontStyle = 0; //default to regular
        if (Objects.equals(splitResult[4], "50") && Objects.equals(splitResult[5], "1")) {
            //Italic;
            fontStyle = Font.ITALIC;
        }
        if (Objects.equals(splitResult[4], "75") && Objects.equals(splitResult[5], "0")) {
            //Bold;
            fontStyle = Font.BOLD;
        }
        if (Objects.equals(splitResult[4], "75") && Objects.equals(splitResult[5], "1")) {
            //Bold | Italic;
            fontStyle = Font.BOLDITALIC;
        }
        return fontStyle;
    }

    private Color getColorFromXPathNode(Object object) throws XPathExpressionException {
        int r = Integer.parseInt(getXpathString("@red", object));
        int g = Integer.parseInt(getXpathString("@green", object));
        int b = Integer.parseInt(getXpathString("@blue", object));
        int a = Integer.parseInt(getXpathString("@alpha", object));
        return new Color(r, g, b, a);
    }
    private Color getRGBColorFromXPathNode(Object object) throws XPathExpressionException {
        int r = Integer.parseInt(getXpathString("@red", object));
        int g = Integer.parseInt(getXpathString("@green", object));
        int b = Integer.parseInt(getXpathString("@blue", object));
        return new Color(r, g, b);
    }

    private void drawImageFromURI(String imageURL, String imageX, String imageY, String imageScaleFactor, Document document) throws IOException {
        if (!Objects.equals(imageURL, "")) {
            URL url = new URL(imageURL);
            InputStream in = url.openStream();
            byte[] imageBytes = in.readAllBytes(); // Read all bytes from the stream
            in.close();
            Image image = Image.getInstance(imageBytes);
            float maxWidth = image.getWidth() * Float.parseFloat(imageScaleFactor); // Maximum width of the image
            float maxHeight = image.getHeight() * Float.parseFloat(imageScaleFactor); // Maximum height of the image
            image.setAbsolutePosition(millimetersToPoints(Float.parseFloat(imageX)),getTopY(document, millimetersToPoints(Float.parseFloat(imageY)) + maxHeight ));
            image.scaleToFit(maxWidth, maxHeight); // Scales the image to fit within the max dimensions while maintaining aspect ratio
            document.add(image);
        }
    }

    private void drawImageFromFilePath(String filePath, String imageX, String imageY, String imageScaleFactor, Document document) throws IOException {
        if (!Objects.equals(filePath, "")) {
            Image image = Image.getInstance(filePath);
            float maxWidth = image.getWidth() * Float.parseFloat(imageScaleFactor); // Maximum width of the image
            float maxHeight = image.getHeight() * Float.parseFloat(imageScaleFactor); // Maximum height of the image
            image.setAbsolutePosition(millimetersToPoints(Float.parseFloat(imageX)),getTopY(document, millimetersToPoints(Float.parseFloat(imageY)) + maxHeight ));
            image.scaleToFit(maxWidth, maxHeight); // Scales the image to fit within the max dimensions while maintaining aspect ratio
            document.add(image);
        }
    }


    private boolean isURLReachable(String urlString) throws IOException {
        int responseCode = 0;
        Properties urlConfigs = new Properties();
        urlConfigs.load(new FileInputStream(configFilePath));
        try {
            URL url = new URL(urlString);
            HttpURLConnection connection = (HttpURLConnection) url.openConnection();
            connection.setRequestMethod(urlConfigs.getProperty("url.reachableMethod")); // Use HEAD for a faster check
            connection.setConnectTimeout(Integer.parseInt(urlConfigs.getProperty("url.connectTimeout")));
            connection.setReadTimeout(Integer.parseInt(urlConfigs.getProperty("url.readTimeout")));
            responseCode = connection.getResponseCode();
            connection.disconnect();
            return (responseCode >= 200 && responseCode < 300);
        } catch (IOException e) {
            logger.error("URL Response Code: {}", responseCode);
            logger.error("URL Error: {}", e.getMessage());
            return false; // URL is not reachable
        }
    }
    private ResultSet getSQLResultSet(String connectionName, String sqlQuery, String FeatureKeys, String ReferenceKey, String DatabaseKey) {
        sqlQuery = sqlQuery.replaceAll("@featurekey", FeatureKeys);
        if (!Objects.equals(ReferenceKey, "")){
            //sqlQuery = sqlQuery.replaceAll("'@referencekey'", ReferenceKey);
            sqlQuery = sqlQuery.replaceAll("@referencekey", ReferenceKey);
        }
        if (!Objects.equals(DatabaseKey, "")){
            //sqlQuery = sqlQuery.replaceAll("'@databasekey'", DatabaseKey);
            sqlQuery = sqlQuery.replaceAll("@databasekey", DatabaseKey);
        }
        Connection connection;
        Statement statement;
        ResultSet resultSet;

        try {
            // 1. Load configuration from file
            Properties dbConfigs = new Properties();
            dbConfigs.load(new FileInputStream(dbConfigFilePath));

            // 2. Get connection details for the specified database
            String urlKey = connectionName + ".url";
            String userKey = connectionName + ".user";
            String passwordKey = connectionName + ".password";
            String driverKey = connectionName + ".driver";

            String dbURL = dbConfigs.getProperty(urlKey);
            String dbUser = dbConfigs.getProperty(userKey);
            String dbPassword = dbConfigs.getProperty(passwordKey);
            String dbDriver = dbConfigs.getProperty(driverKey);

            if (dbURL == null || dbUser == null || dbPassword == null || dbDriver == null) {
                throw new IllegalArgumentException("Missing database configuration for: " + connectionName);
            }

            // 3. Load the JDBC driver
            Class.forName(dbDriver);
            // 4. Establish the database connection
            connection = DriverManager.getConnection(dbURL, dbUser, dbPassword);
            // 5. Create a statement and execute the query
            statement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
            resultSet = statement.executeQuery(sqlQuery);
            // 6. Process the result set
            return resultSet;

        } catch (IOException | ClassNotFoundException | SQLException | IllegalArgumentException e) {
            logger.error(e.getMessage());
            logger.error(Arrays.toString(e.getStackTrace()));
            logger.error("SQL: " + sqlQuery);
        }
        return null;
    }

    private int getRowCount(ResultSet res){
        int totalRows;
        try {
            res.last();
            totalRows = res.getRow();
            res.beforeFirst();
        }
        catch(Exception ex)  {
            return 0;
        }
        return totalRows ;
    }

    private void drawForeignPDFPages(String foreignDoc, String foreignDocImportPage, String foreignDocType, Document document, PdfWriter pdfwriter) throws IOException {
        PdfReader reader = null;

        if (foreignDocType.equalsIgnoreCase("web")) {
            //web
            if (isURLReachable(foreignDoc)){
                reader = new PdfReader(foreignDoc);
            }
        } else {
            //local
            reader = new PdfReader(foreignDoc);
        }

        if (reader != null) {
            int pageNo;
            if (foreignDocImportPage.contains("*")) {
                //import all pages
                for (pageNo = 1; pageNo <= reader.getNumberOfPages(); pageNo++) {
                    drawForeignPDFPage(pageNo, document, pdfwriter, reader);
                }
            } else {
                //import pages and\or page ranges
                if (foreignDocImportPage.contains(",")) {
                    //e.g. 1,2,6 or 1,2,5-6
                    //Split on ","
                    String[] splitByComma = foreignDocImportPage.split(",");
                    for (String s : splitByComma) {
                        //check for "-"
                        if (s.contains("-")) {
                            //e.g. 5-6
                            //Split on "-"
                            String[] splitByDash = s.split("-");
                            int importPageRangeStartNo = Integer.parseInt(splitByDash[0]);
                            int importPageRangeEndNo = Integer.parseInt(splitByDash[1]);
                            for (pageNo = importPageRangeStartNo; pageNo <= importPageRangeEndNo; pageNo++) {
                                drawForeignPDFPage(pageNo, document, pdfwriter, reader);
                            }
                        } else {
                            //e.g. 1
                            pageNo = Integer.parseInt(s);
                            drawForeignPDFPage(pageNo, document, pdfwriter, reader);
                        }
                    }
                } else {
                    //e.g. 1 or 5-6
                    //check for "-"
                    if (foreignDocImportPage.contains("-")) {
                        //e.g. 5-6
                        //Split on "-"
                        String[] splitByDash = foreignDocImportPage.split("-");
                        int importPageRangeStartNo = Integer.parseInt(splitByDash[0]);
                        int importPageRangeEndNo = Integer.parseInt(splitByDash[1]);
                        for (pageNo = importPageRangeStartNo; pageNo <= importPageRangeEndNo; pageNo++) {
                            drawForeignPDFPage(pageNo, document, pdfwriter, reader);
                        }
                    } else {
                        //e.g. 1
                        pageNo = Integer.parseInt(foreignDocImportPage);
                        drawForeignPDFPage(pageNo, document, pdfwriter, reader);
                    }
                }
            }
            reader.close();
        }
    }

    private void drawForeignPDFPages(String foreignDocImportPage, PdfReader reader, Document document, PdfWriter pdfwriter) {
        int pageNo;
        if(foreignDocImportPage.contains("*")){
            //import all pages
            for(pageNo = 1; pageNo <= reader.getNumberOfPages(); pageNo++){
                drawForeignPDFPage(pageNo, document, pdfwriter, reader);
            }
        } else {
            //import pages and\or page ranges
            if(foreignDocImportPage.contains(",")){
                //e.g. 1,2,6 or 1,2,5-6
                //Split on ","
                String[] splitByComma = foreignDocImportPage.split(",");
                for (String s : splitByComma) {
                    //check for "-"
                    if (s.contains("-")) {
                        //e.g. 5-6
                        //Split on "-"
                        String[] splitByDash = s.split("-");
                        int importPageRangeStartNo = Integer.parseInt(splitByDash[0]);
                        int importPageRangeEndNo = Integer.parseInt(splitByDash[1]);
                        for(pageNo = importPageRangeStartNo; pageNo <= importPageRangeEndNo; pageNo++){
                            drawForeignPDFPage(pageNo, document, pdfwriter, reader);
                        }
                    } else {
                        //e.g. 1
                        pageNo = Integer.parseInt(s);
                        drawForeignPDFPage(pageNo, document, pdfwriter, reader);
                    }
                }
            } else {
                //e.g. 1 or 5-6
                //check for "-"
                if (foreignDocImportPage.contains("-")) {
                    //e.g. 5-6
                    //Split on "-"
                    String[] splitByDash = foreignDocImportPage.split("-");
                    int importPageRangeStartNo = Integer.parseInt(splitByDash[0]);
                    int importPageRangeEndNo = Integer.parseInt(splitByDash[1]);
                    for(pageNo = importPageRangeStartNo; pageNo <= importPageRangeEndNo; pageNo++){
                        drawForeignPDFPage(pageNo, document, pdfwriter, reader);
                    }
                } else {
                    //e.g. 1
                    pageNo = Integer.parseInt(foreignDocImportPage);
                    drawForeignPDFPage(pageNo, document, pdfwriter, reader);
                }
            }
        }
    }

    private void drawForeignPDFPage(int pageNo, Document document, PdfWriter pdfwriter, PdfReader reader) {
        document.setPageSize(reader.getPageSize(pageNo));
        document.newPage();
        PdfImportedPage page = pdfwriter.getImportedPage(reader, pageNo);
        pdfwriter.getDirectContent().addTemplate(page, 0, 0);
    }

    public int[] StreamSplitStringToIntArray (String input) {
        return Arrays.stream(input.split(","))
                .map(String::trim)
                .mapToInt(Integer::parseInt)
                .toArray();
    }

    private String decode(String value) {
        return URLDecoder.decode(value, StandardCharsets.UTF_8);
    }

    private String keyEncode4URL(String key) {
        if (key.matches("\\d+")) {
            return key;
        } else {
            return URLEncoder.encode("'" + key + "'", StandardCharsets.UTF_8);
        }
    }


    // Helper to get the Y coordinate relative to the top
    // OpenPDF defaults to 0,0 at bottom left, whereas QGIS QPT Templates have 0,0 at top left
    private float getTopY(Document document, float yFromTop) {
        return document.getPageSize().getHeight() - yFromTop;
    }

    //XPath Helpers
    private NodeList getXpathNodeList(String expression, Object object) throws XPathExpressionException {
        XPath xpath = XPathFactory.newInstance().newXPath();
        return (NodeList) xpath.evaluate(expression,object,XPathConstants.NODESET);
    }
    private Node getXpathNode(String expression, Object object) throws XPathExpressionException {
        XPath xpath = XPathFactory.newInstance().newXPath();
        return (Node) xpath.evaluate(expression,object,XPathConstants.NODE);
    }
    private String getXpathString(String expression, Object object) throws XPathExpressionException {
        XPath xpath = XPathFactory.newInstance().newXPath();
        return (String) xpath.evaluate(expression,object,XPathConstants.STRING);
    }


    private String getQueryStringPropertyName (String dataURL) throws URISyntaxException {
        URI uri = new URI(dataURL);
        String querystring = uri.getQuery();
        String propertyName = "";
        if (querystring != null)
        {
            Map<String, String> querystringMap = Arrays.stream(querystring.split("&"))
                    .map(param -> param.split("=", 2))
                    .collect(Collectors.toMap(
                            pair -> decode(pair[0]),              // Key
                            pair -> pair.length > 1 ? decode(pair[1]) : "" // Value
                    ));
            if (querystringMap.containsKey("propertyName")) {
                propertyName = querystringMap.get("propertyName");
            }
        }
        return propertyName;
    }


}


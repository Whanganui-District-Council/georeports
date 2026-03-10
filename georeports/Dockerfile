# --- STAGE 1: The Builder ---
FROM ubuntu:22.04 AS builder

# Avoid prompts during installation
ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y \
    software-properties-common \
    curl \
    wget \
    fontconfig \
    build-essential \
    cmake \
    swig \
    ant \
    libpq-dev \
    libxerces-c-dev \
    libexpat1-dev \
    libcurl4-openssl-dev \
    libproj-dev \
    openjdk-17-jdk \
    python3-dev \
    && add-apt-repository multiverse \
    && apt-get update

ENV JAVA_HOME=/usr/lib/jvm/java-17-openjdk-amd64
ENV GDAL_VERSION=3.8.4

WORKDIR /build
RUN wget https://github.com/OSGeo/gdal/releases/download/v${GDAL_VERSION}/gdal-${GDAL_VERSION}.tar.gz \
    && tar -xf gdal-${GDAL_VERSION}.tar.gz

WORKDIR /build/gdal-${GDAL_VERSION}/build
RUN cmake .. \
    -DBUILD_PYTHON_BINDINGS=OFF \
    -DBUILD_JAVA_BINDINGS=ON \
    -DCMAKE_INSTALL_PREFIX=/usr/local/gdal_dist \
    -DBUILD_SHARED_LIBS=ON \
    -DWITH_XERCES_C=ON \
    -DXERCES_C_INCLUDE_DIR=/usr/include/xercesc \
    -DXERCES_C_LIBRARY=/usr/lib/x86_64-linux-gnu/libxerces-c.so \
    && cmake --build . -j$(nproc) \
    && cmake --install .

# --- STAGE 2: The Slim Runtime ---
# FROM eclipse-temurin:17-jre-jammy
FROM tomcat:9.0.115-jdk17-temurin-jammy

RUN apt-get update && apt-get install -y \
software-properties-common \
    curl \
    wget \
    fontconfig \
    && add-apt-repository multiverse \
    && apt-get update

# Install GDAL 3.8.4
# Note: Jammy's default repo has older GDAL. We use the UbuntuGIS PPA for newer versions.
RUN add-apt-repository ppa:ubuntugis/ubuntugis-unstable
# We still need PROJ and CURL runtime libraries, but NOT the compilers
RUN apt-get update && apt-get install -y \
    gdal-bin \
    libgdal-dev \
    python3-gdal \
    libproj22 \
    libcurl4 \
    libpq-dev \
    libxerces-c-dev \
    python3-dev \
    && apt-get update

# Copy the compiled binaries from the builder stage
# /usr/local/gdal_dist contains the .so files and the .jar
# COPY --from=builder /usr/local/gdal_dist /usr/local/simon
COPY --from=builder /usr/local/gdal_dist/lib /usr/local/lib
COPY --from=builder /usr/local/gdal_dist/share/java /usr/local/share/java

# Link the GDAL JAR to Tomcat's library folder
# On Ubuntu, libgdal-java usually places the jar in /usr/share/java/
RUN ln -s /usr/local/share/java/gdal-3.8.4.jar /usr/local/tomcat/lib/gdal-3.8.4.jar

# Tell the OS and Java where to find the native libraries
ENV LD_LIBRARY_PATH=/usr/local/lib:/usr/local/lib/jni:$LD_LIBRARY_PATH
# ENV CLASSPATH=/usr/local/share/java/gdal-3.8.4.jar:$CLASSPATH
ENV CLASSPATH=/usr/local/tomcat/lib/gdal-3.8.4.jar:$CLASSPATH

# Update linker cache
RUN ldconfig

# Add MS Fonts
# Pre-accept the Microsoft EULA
# This is the "magic" line that prevents the build from hanging
RUN echo "ttf-mscorefonts-installer msttcorefonts/accepted-mscorefonts-eula select true" | debconf-set-selections
RUN apt-get install -y ttf-mscorefonts-installer
# Refresh the font cache so the system (and Java) can see them
RUN fc-cache -fv
# (Optional) Check if fonts are installed
RUN fc-list | grep -i "Arial"



# Expose Tomcat port
EXPOSE 8080

COPY ./target/georeports /usr/local/tomcat/webapps/georeports

# Start Tomcat
CMD ["catalina.sh", "run"]
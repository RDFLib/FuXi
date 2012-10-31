<?xml version="1.0" encoding="UTF-8" ?>
<!--
    XSLT mapping from the XML grammar of  RIF-Core 
    to the RIF In RDF vocabulary (as an XML/RDF serialization)
-->
<!DOCTYPE xsl:stylesheet [
  <!ENTITY rif  "http://www.w3.org/2007/rif#">
  <!ENTITY xs   "http://www.w3.org/2001/XMLSchema#">
]>
<xsl:stylesheet 
    version="1.0"
    xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
    xmlns:rif="http://www.w3.org/2007/rif#"
    xmlns    ="http://www.w3.org/2007/rif#"
    xmlns:uri="http://xsltsl.org/uri"
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
	<xsl:output encoding="UTF-8" indent="yes" method="xml" />
    <xsl:include href="uri.xsl" />
	<xsl:template match="/">
	    <xsl:apply-templates select="*" mode="class-element"/>
	</xsl:template>
	
	<xsl:template match="rif:Var" mode="class-element">
	    <xsl:copy>
	       <rif:varname>
	           <xsl:value-of select="."/>
	       </rif:varname>
	    </xsl:copy>
	</xsl:template>

	<xsl:template match="rif:Const" mode="class-element">
	    <xsl:copy>
    	    <xsl:choose>
    	      <xsl:when test="@type='&rif;iri'">
                  <rif:constIRI rdf:datatype="http://www.w3.org/2001/XMLSchema#anyURI">
                      <xsl:choose>
                        <xsl:when test="not(contains(., ':')) and /rif:Document/@xml:base">
                            <xsl:call-template name="uri:resolve-uri">
                                <xsl:with-param name="reference" select="." />
                                <xsl:with-param name="base" select="/rif:Document/@xml:base" />
                            </xsl:call-template>
                        </xsl:when>
                        <xsl:otherwise>
                            <xsl:value-of select="."/>
                        </xsl:otherwise>
                      </xsl:choose>
                      
                  </rif:constIRI>
    	      </xsl:when>
    	      <xsl:when test="@type='&rif;local'">
                  <rif:constname>
                    <xsl:value-of select="."/>
                  </rif:constname>
    	      </xsl:when>
    	      <xsl:when test="@type='http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral'">
                  <xsl:element name="rif:value" namespace="&rif;">
                    <xsl:if test="contains(.,'@')">
                        <xsl:attribute name="xml:lang">
                            <xsl:value-of select="substring-after(.,'@')"/>
                        </xsl:attribute>
                    </xsl:if>
                    <xsl:value-of select="substring-before(.,'@')"/>
                  </xsl:element>
    	      </xsl:when>
    	      <xsl:otherwise>
                  <rif:value rdf:datatype="{@type}">
                    <xsl:value-of select="."/>
                  </rif:value>
    	      </xsl:otherwise>
    	    </xsl:choose>	       
	    </xsl:copy>
	</xsl:template>
	
	<xsl:template match="rif:slot" mode="mode3">
	    <rif:Slot>
	       <rif:slotkey>
	           <xsl:apply-templates select="*[1]" mode="class-element"/>
	       </rif:slotkey>
	       <rif:slotvalue>
	           <xsl:apply-templates select="*[2]" mode="class-element"/>
	       </rif:slotvalue>
	    </rif:Slot>
	</xsl:template>
	
	<xsl:template name="handle-child-element">
	    <!-- Not sure Mode 2 occurs in RIF-Core outside of exceptions in table 3  -->
	    <xsl:choose>
	      <xsl:when test="local-name() != 'slot' and @ordered='yes'">
	          <!-- Mode 0 -->
              <xsl:element name="{name()}" namespace="&rif;">
                  <xsl:attribute 
                       name="rdf:parseType" 
                       namespace="http://www.w3.org/1999/02/22-rdf-syntax-ns#">Collection</xsl:attribute>
                  <xsl:apply-templates select="*" mode="class-element" />
              </xsl:element>
	      </xsl:when>
	      <!--xsl:when test="local-name() = 'payload' or 
	                      local-name() = 'profile' or 
	                      local-name() = 'object'"-->
	        <!-- Mode 1 -->
            <!--xsl:copy>
                <xsl:apply-templates select="*" mode="class-element" />
            </xsl:copy>
	      </xsl:when-->
	      <xsl:otherwise>
	          <!-- Mode 1 -->
	          <xsl:copy>
                  <xsl:apply-templates select="*" mode="class-element" />
	          </xsl:copy>
	      </xsl:otherwise> 
	    </xsl:choose>
	</xsl:template>

	<xsl:template match="*" mode="class-element">
	    <xsl:variable name="focusNode" select="local-name()" />
	    <xsl:copy>
	        <xsl:if test="$focusNode = 'Document' and @xml:base">
	           <xsl:copy-of select="@xml:base" />
	        </xsl:if>
	        <xsl:if test="rif:id/rif:Const[@type='&rif;iri']">
	           <xsl:attribute name="rdf:about" 
	                          namespace="http://www.w3.org/1999/02/22-rdf-syntax-ns#">
                   <xsl:value-of select="rif:id/rif:Const"/>
	           </xsl:attribute>
	        </xsl:if>
	        
	        <xsl:for-each select="*">
	            <xsl:variable name="childName" select="local-name()" />
                <xsl:if test="$childName != 'slot'                     and 
                        not($focusNode = 'Document' and $childName ='directive') and
                        not($focusNode = 'Group'    and $childName ='sentence')  and 
                        not($focusNode = 'Forall'   and $childName ='declare')   and 
                        not($focusNode = 'Exists'   and $childName ='declare')   and 
                        not($focusNode = 'And'      and $childName ='formula')   and 
                        not($focusNode = 'Or'       and $childName ='formula')   and
                        $childName != 'id'">
                    <xsl:call-template name="handle-child-element"/>
                </xsl:if>
	        </xsl:for-each>	        
	        
            <xsl:if test="rif:slot[@ordered='yes']">
                <!-- Mode 3 -->
                <rif:slots rdf:parseType="Collection">
                    <xsl:apply-templates select="rif:slot" mode="mode3" />
                </rif:slots>
            </xsl:if>
            
            <!-- Mode 2 exceptions -->
            <xsl:if test="$focusNode = 'Document'">
                <rif:directives rdf:parseType="Collection">
                    <xsl:apply-templates select="rif:directive/*" mode="class-element"/>
                </rif:directives>                
            </xsl:if>
            <xsl:if test="$focusNode = 'Group'">
                <rif:sentences rdf:parseType="Collection">
                    <xsl:apply-templates select="rif:sentence/*" mode="class-element"/>
                </rif:sentences>
            </xsl:if>
            <xsl:if test="$focusNode = 'Forall'">
                <rif:vars rdf:parseType="Collection">
                    <xsl:apply-templates select="rif:declare/*" mode="class-element"/>
                </rif:vars>                
            </xsl:if>
            <xsl:if test="$focusNode = 'Exists'">
                <rif:vars rdf:parseType="Collection">
                    <xsl:apply-templates select="rif:declare/*" mode="class-element"/>
                </rif:vars>                
            </xsl:if>
            <xsl:if test="$focusNode = 'And'">
                <rif:formulas rdf:parseType="Collection">
                    <xsl:apply-templates select="rif:formula/*" mode="class-element"/>
                </rif:formulas>                
            </xsl:if>
            <xsl:if test="$focusNode = 'Or'">
                <rif:formulas rdf:parseType="Collection">
                    <xsl:apply-templates select="rif:formula/*" mode="class-element"/>
                </rif:formulas>                
            </xsl:if>
        </xsl:copy>
	</xsl:template>			
</xsl:stylesheet>
